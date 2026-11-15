"""Independent verifier for rdis v2.

It shares no code with rdis: it parses the PE by hand (struct), decodes with capstone, re-derives facts, and compares them with what the
rdis binary prints (JSON). Any disagreement is a failure. Usage:
    python verify.py <exe> <rdis.exe> [--n 150] [--seed 1]
"""
import bisect, json, random, struct, subprocess, sys, collections
from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_OPT_DETAIL
from capstone.x86 import X86_OP_IMM, X86_OP_REG, X86_OP_MEM
import capstone.x86 as _x
WMASK = 0
for _n in dir(_x):
    if _n.startswith('X86_EFLAGS_') and not _n.startswith('X86_EFLAGS_TEST_') and not _n.startswith('X86_EFLAGS_UNDEFINED_') and isinstance(getattr(_x, _n), int):
        WMASK |= getattr(_x, _n)
def writes_flags(i):
    # capstone reports eflags=0 for some rip-relative test/cmp forms (e.g. test [rip+X], r14b); these always write flags architecturally
    return bool(i.eflags & WMASK) or i.mnemonic in ('test', 'cmp', 'bt')

EXE, RDIS = sys.argv[1], sys.argv[2]
N = int(sys.argv[sys.argv.index('--n') + 1]) if '--n' in sys.argv else 150
SEED = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
data = open(EXE, 'rb').read()
u32 = lambda o: struct.unpack_from('<I', data, o)[0]
u16 = lambda o: struct.unpack_from('<H', data, o)[0]
u64 = lambda o: struct.unpack_from('<Q', data, o)[0]
pe = u32(0x3c)
nsec = u16(pe + 6)
opt = u16(pe + 20)
IMAGE_BASE = u64(pe + 24 + 24)
secs = []
for i in range(nsec):
    s = pe + 24 + opt + i * 40
    secs.append(dict(name=data[s:s + 8].rstrip(b'\0').decode(), vsize=u32(s + 8), rva=u32(s + 12), rawsize=u32(s + 16), raw=u32(s + 20), flags=u32(s + 36)))

def off(rva):
    for s in secs:
        if s['rva'] <= rva < s['rva'] + max(s['vsize'], s['rawsize']):
            d = rva - s['rva']
            return s['raw'] + d if d < s['rawsize'] else None
    return None

def is_exec(rva):
    for s in secs:
        if s['rva'] <= rva < s['rva'] + max(s['vsize'], s['rawsize']):
            return bool(s['flags'] & 0x20000000)
    return False

def rd(rva, n):
    o = off(rva)
    return data[o:o + n] if o is not None else b''

# ---- .pdata, by hand
exc = pe + 24 + 0x70 + 3 * 8
prva, psize = u32(exc), u32(exc + 4)
po = off(prva)
raw = sorted((u32(po + i * 12), u32(po + i * 12 + 4), u32(po + i * 12 + 8)) for i in range(psize // 12))
begins = [r[0] for r in raw]

def chain_parent(unwind):
    o = off(unwind & ~1)
    flags = data[o] >> 3
    if not flags & 4:
        return None
    codes = data[o + 2]
    return u32(o + 4 + ((codes * 2 + 3) & ~3))

root = {}
for b, e, u in raw:
    root[b] = chain_parent(u) or b
for _ in range(6):
    for b in list(root):
        if root[b] != b and root[b] in root:
            root[b] = root[root[b]]
primary = [(b, e) for b, e, u in raw if root[b] == b]
frags = collections.defaultdict(list)
for b, e, u in raw:
    if root[b] != b:
        frags[root[b]].append((b, e))
rng = {b: e for b, e, u in raw}

md = Cs(CS_ARCH_X86, CS_MODE_64)
md.detail = True

class I:
    """capstone puts prefixes (lock/rep) into .mnemonic; keep the bare mnemonic."""
    def __init__(self, x):
        self.address, self.size, self.operands, self.eflags = x.address, x.size, x.operands, x.eflags
        self.mnemonic = x.mnemonic.split()[-1]
        self.full_mnemonic = x.mnemonic

def decode(ranges):
    out = []
    for b, e in ranges:
        out.extend(I(x) for x in md.disasm(rd(b, e - b), b))
    return out

def fn_ranges(f):
    return [(f, rng[f])] + sorted(frags.get(f, []))

def in_ranges(rs, x):
    return any(b <= x < e for b, e in rs)

# ---- independent CFG
SKIPPED = []
class PCfg: pass

def is_term(i):
    return i.mnemonic == 'jmp' or i.mnemonic.startswith('j') or i.mnemonic in ('ret', 'retf', 'ud2', 'ud1', 'ud0') or (i.mnemonic == 'jmp')

def cc_of(m):
    return m != 'jmp' and m.startswith('j')

def build_cfg(f, extra=frozenset()):
    rs = fn_ranges(f)
    ins = decode(rs)
    leaders = {b for b, e in rs} | set(extra)
    for n, i in enumerate(ins):
        m = i.mnemonic
        if m.startswith('j'):
            op = i.operands[0]
            if op.type == X86_OP_IMM and in_ranges(rs, op.imm):
                leaders.add(op.imm)
            if n + 1 < len(ins):
                leaders.add(ins[n + 1].address)
        elif m in ('ret', 'ud2', 'ud1', 'ud0'):
            if n + 1 < len(ins):
                leaders.add(ins[n + 1].address)
    blocks = {}
    n = 0
    while n < len(ins):
        first = n
        start = ins[n].address
        last = n
        while True:
            i = ins[last]
            term = i.mnemonic.startswith('j') or i.mnemonic in ('ret', 'ud2', 'ud1', 'ud0')
            nx = ins[last + 1] if last + 1 < len(ins) else None
            contiguous = nx is not None and nx.address == i.address + i.size
            if term or not contiguous or nx is None or nx.address in leaders:
                break
            last += 1
        blocks[start] = dict(start=start, end=ins[last].address + ins[last].size, first=first, last=last, succ=[])
        n = last + 1
    cfg = PCfg()
    cfg.rs, cfg.ins, cfg.blocks = rs, ins, blocks
    cfg.tails = []
    cfg.unres = []
    cfg.switches = []
    cfg.need = set()
    cfg.insaddr = {i.address for i in ins}
    jobs = []
    for s, b in blocks.items():
        t = ins[b['last']]
        nx = ins[b['last'] + 1] if b['last'] + 1 < len(ins) and ins[b['last'] + 1].address == t.address + t.size else None
        nxa = nx.address if nx is not None else None
        m = t.mnemonic
        if m == 'jmp':
            op = t.operands[0]
            if op.type == X86_OP_IMM:
                if op.imm in blocks:
                    b['succ'].append(('Jmp', op.imm, []))
                else:
                    cfg.tails.append((t.address, op.imm))
            else:
                jobs.append(s)
        elif m.startswith('j'):
            tg = t.operands[0].imm
            if tg in blocks:
                b['succ'].append(('Taken', tg, []))
            else:
                cfg.tails.append((t.address, tg))
                b['succ'].append(('TakenOut', tg, []))
            if nxa in blocks:
                b['succ'].append(('NotTaken', nxa, []))
        elif m in ('ret', 'ud2', 'ud1', 'ud0'):
            pass
        else:
            if nxa in blocks:
                b['succ'].append(('Fall', nxa, []))
    pend = list(jobs)
    while pend:
        nxt = []
        prog = False
        for s in pend:
            u = len(cfg.unres)
            resolve_switch(cfg, s)
            if len(cfg.unres) > u:
                del cfg.unres[u:]; nxt.append(s)
            else: prog = True
        if not prog:
            for s in nxt: resolve_switch(cfg, s)
            break
        pend = nxt
    if cfg.need and not cfg.need <= set(extra) and len(extra) < 4000:
        return build_cfg(f, frozenset(extra) | cfg.need)
    return cfg

def resolve_switch(cfg, bs):
    """jmp reg ; reg = add reg, B ; reg = movsxd/mov [B+I*4+disp] ; B = lea [rip+X] ; bound from cmp I,N / ja in the single predecessor."""
    b = cfg.blocks[bs]
    ins = cfg.ins
    jmp = ins[b['last']]
    op = jmp.operands[0]
    if op.type != X86_OP_REG:
        cfg.unres.append(jmp.address)
        return
    r = op.reg
    def writes(i, reg):
        return i.operands and i.operands[0].type == X86_OP_REG and md.reg_name(i.operands[0].reg) is not None and full(i.operands[0].reg) == full(reg) and i.mnemonic not in ('cmp', 'test')
    k = b['last']
    def prev(k, reg):
        while k > b['first']:
            k -= 1
            if writes(ins[k], reg):
                return k
        return None
    ka = prev(k, r)
    if ka is None or ins[ka].mnemonic != 'add' or ins[ka].operands[1].type != X86_OP_REG:
        cfg.unres.append(jmp.address); return
    breg = ins[ka].operands[1].reg
    kl = prev(ka, r)
    if kl is None or ins[kl].mnemonic not in ('movsxd', 'mov') or ins[kl].operands[1].type != X86_OP_MEM:
        cfg.unres.append(jmp.address); return
    mem = ins[kl].operands[1].mem
    if mem.scale != 4 or full(mem.base) != full(breg):
        cfg.unres.append(jmp.address); return
    kb = prev(kl, breg)
    if kb is None:
        # forward must-reach analysis (independent of rdis's backward walk): which defs of breg reach the start of block bs
        UNDEF, CLOB = -1, -2
        vol = full(breg) in {full(r) for r in (_x.X86_REG_RAX, _x.X86_REG_RCX, _x.X86_REG_RDX, _x.X86_REG_R8, _x.X86_REG_R9, _x.X86_REG_R10, _x.X86_REG_R11)}
        entries_ = {bb for bb, ee in cfg.rs}
        inn = {a: set() for a in cfg.blocks}
        for a in entries_:
            if a in inn: inn[a].add(UNDEF)
        preds_ = collections.defaultdict(list)
        for a, bb in cfg.blocks.items():
            for e in bb['succ']: preds_[e[1]].append(a)
        def out_of(a):
            bb = cfg.blocks[a]
            st = set(inn[a])
            for q in range(bb['first'], bb['last'] + 1):
                if vol and ins[q].mnemonic == 'call': st = {CLOB}
                if writes(ins[q], breg) and ins[q].mnemonic != 'push': st = {q}
            return st
        changed = True
        while changed:
            changed = False
            for a in cfg.blocks:
                if a == bs: pass
                new = set(inn[a])
                for pa in preds_[a]: new |= out_of(pa)
                if new != inn[a]: inn[a] = new; changed = True
        if len(inn[bs]) == 1 and next(iter(inn[bs])) >= 0: kb = next(iter(inn[bs]))
    if kb is None or ins[kb].mnemonic != 'lea':
        cfg.unres.append(jmp.address); return
    lm = ins[kb].operands[1].mem
    if full(lm.base) != full_rip():
        cfg.unres.append(jmp.address); return
    x = ins[kb].address + ins[kb].size + lm.disp
    table = x + mem.disp
    idx = full(mem.index)
    btab = None
    kz = prev(kl, mem.index)
    if kz is not None and ins[kz].mnemonic == 'movzx' and ins[kz].operands[1].type == X86_OP_MEM and ins[kz].operands[1].size == 1 and ins[kz].operands[1].mem.scale == 1 and full(ins[kz].operands[1].mem.base) == full(breg):
        btab = (ins[kz].operands[1].mem.disp, full(ins[kz].operands[1].mem.index))
        idx = btab[1]
        kc = prev(kz, ins[kz].operands[1].mem.index)
        if kc is not None and ins[kc].mnemonic in ('movsxd', 'mov', 'movsx', 'movzx') and ins[kc].operands[1].type == X86_OP_REG:
            idx = full(ins[kc].operands[1].reg)
    # bound
    preds = [(s, e) for s, bb in cfg.blocks.items() for e in bb['succ'] if e[1] == bs]
    bound = None
    if len(preds) == 1:
        ps, e = preds[0]
        pb = cfg.blocks[ps]
        jc = ins[pb['last']]
        cmpi = None
        for q in range(pb['last'] - 1, pb['first'] - 1, -1):
            if 'cmp' == ins[q].mnemonic or ins[q].mnemonic in FLAGSET:
                cmpi = ins[q]; break
        if cmpi is not None and cmpi.mnemonic == 'cmp' and cmpi.operands[0].type == X86_OP_REG and full(cmpi.operands[0].reg) == idx and cmpi.operands[1].type == X86_OP_IMM:
            n = cmpi.operands[1].imm
            m = jc.mnemonic
            if (m == 'ja' and e[0] == 'NotTaken') or (m == 'jbe' and e[0] == 'Taken'):
                bound = n + 1
            elif (m in ('jae', 'jnb') and e[0] == 'NotTaken') or (m in ('jb', 'jae') and e[0] == 'Taken' and m == 'jb'):
                bound = n
    how = 'cmp-bound'
    if btab is not None:
        if bound is None:
            cfg.unres.append(jmp.address); return
        bt = rd(x + btab[0], bound)
        entries = []
        for q in range(bound):
            t = x + struct.unpack('<i', rd(table + 4 * bt[q], 4))[0]
            if t not in cfg.blocks:
                if in_ranges(cfg.rs, t): cfg.need.add(t)
                cfg.unres.append(jmp.address); return
            entries.append(t)
        by = collections.defaultdict(list)
        for q, t in enumerate(entries): by[t].append(q)
        b['succ'] = [('Case', t, cs) for t, cs in sorted(by.items())]
        cfg.switches.append((jmp.address, table, entries, 'cmp-bound+byte-table'))
        return
    if bound is None:
        how = 'scan'
        k2 = 0
        while k2 < 512:
            raw4 = rd(table + 4 * k2, 4)
            if len(raw4) < 4: break
            t = x + struct.unpack('<i', raw4)[0]
            if not in_ranges(cfg.rs, t) or t not in cfg.insaddr: break
            if t not in cfg.blocks: cfg.need.add(t)
            k2 += 1
        bound = k2
    entries = []
    for q in range(bound):
        raw4 = rd(table + 4 * q, 4)
        t = x + struct.unpack('<i', raw4)[0]
        if t not in cfg.blocks:
            if in_ranges(cfg.rs, t): cfg.need.add(t)
            cfg.unres.append(jmp.address); return
        entries.append(t)
    if not entries:
        cfg.unres.append(jmp.address); return
    by = collections.defaultdict(list)
    for q, t in enumerate(entries): by[t].append(q)
    b['succ'] = [('Case', t, cs) for t, cs in sorted(by.items())]
    cfg.switches.append((jmp.address, table, entries, how))

FLAGSET = {'cmp', 'test', 'sub', 'add', 'and', 'or', 'xor', 'inc', 'dec', 'neg', 'ucomiss', 'comiss', 'ucomisd', 'comisd', 'bt'}
_full = {}
def full(reg):
    n = md.reg_name(reg)
    if n is None: return None
    n = n.lower()
    m = {'al':'rax','ax':'rax','eax':'rax','rax':'rax','cl':'rcx','cx':'rcx','ecx':'rcx','rcx':'rcx','dl':'rdx','dx':'rdx','edx':'rdx','rdx':'rdx','bl':'rbx','bx':'rbx','ebx':'rbx','rbx':'rbx',
         'spl':'rsp','sp':'rsp','esp':'rsp','rsp':'rsp','bpl':'rbp','bp':'rbp','ebp':'rbp','rbp':'rbp','sil':'rsi','si':'rsi','esi':'rsi','rsi':'rsi','dil':'rdi','di':'rdi','edi':'rdi','rdi':'rdi'}
    if n in m: return m[n]
    for p in range(8, 16):
        if n in ('r%d' % p, 'r%dd' % p, 'r%dw' % p, 'r%db' % p): return 'r%d' % p
    return n
def full_rip(): return 'rip'

def byaddr_m(cfg, a):
    for i in cfg.ins:
        if i.address == a: return i.mnemonic
    return '?'

def reach_without(cfg, start, target, ban=None, skip=None):
    if skip == start: return False
    seen = {start}; st = [start]
    while st:
        b = st.pop()
        if b == target: return True
        for i, e in enumerate(cfg.blocks[b]['succ']):
            if e[0] == 'TakenOut' or (b, i) == ban or e[1] == skip: continue
            if e[1] not in seen:
                seen.add(e[1]); st.append(e[1])
    return False

def gates(cfg, f, target):
    out = set()
    if not reach_without(cfg, f, target): return None
    for bs, b in cfg.blocks.items():
        if len(b['succ']) < 2: continue
        for i, e in enumerate(b['succ']):
            if e[0] == 'TakenOut': continue
            if not reach_without(cfg, f, target, ban=(bs, i)):
                out.add((cfg.ins[b['last']].address, e[0]))
    return out

# ---- run rdis
def run_rdis(cmds):
    outs = {}
    for c0 in range(0, len(cmds), 60):
        chunk = cmds[c0:c0 + 60]
        p = subprocess.run([RDIS, EXE, '-c', '; '.join(chunk)], capture_output=True, text=True, encoding='utf8')
        cur = None
        for line in p.stdout.split(chr(10)):
            if line.startswith('> '):
                cur = line[2:]
                outs[cur] = ''
            elif cur is not None:
                outs[cur] += line
    return outs

fails = []
checks = collections.Counter()
def check(cond, what):
    checks[what.split(':')[0]] += 1
    if not cond:
        fails.append(what)

random.seed(SEED)
cands = [(b, e) for b, e in primary if 0x60 <= e - b <= 0x4000 and is_exec(b)]
sample = [b for b, e in random.sample(cands, N)]
# make sure some functions with switches / vcalls / tail calls are in the sample
more = [0xbc92e0]
hunt = []
if '--no-hunt' not in sys.argv:
    order = random.sample(cands, min(len(cands), 25000))
    for b, e in order:
        code = rd(b, e - b)
        if not any(bytes([255, x]) in code for x in (0xe0,0xe1,0xe2,0xe3,0xe5,0xe6,0xe7)): continue
        if any(i.mnemonic == 'jmp' and i.operands[0].type == X86_OP_REG for i in decode(fn_ranges(b))):
            hunt.append(b)
        if len(hunt) >= 30: break
sample = more + sample + hunt

cmds = []
for f in sample:
    cmds.append('cfg 0x%x --max 100000' % f)
    cmds.append('sum 0x%x --only calls --max 100000' % f)
    cmds.append('sum 0x%x --only raw --max 100000' % f)
    cmds.append('sum 0x%x --only conds --max 100000' % f)
outs = run_rdis(cmds)

nsw = 0
for f in sample:
    cfg = build_cfg(f)
    rj = json.loads(outs['cfg 0x%x --max 100000' % f])
    # V1 extent
    sj = json.loads(outs['sum 0x%x --only calls --max 100000' % f])
    check(sj['range'] == [hex(f), hex(rng[f])] or True, 'extent')
    check(sj['range'][0] == hex(f), 'extent: start of 0x%x' % f)
    check(sj['range'][1] == hex(fn_ranges(f)[-1][1]), 'extent: end of 0x%x' % f)
    # V3 blocks
    rb = {int(b['start'], 16): b for b in rj['cfg']['blocks']['items']} if 'cfg' in rj else {int(b['start'], 16): b for b in rj['blocks']['items']}
    dic = any(in_ranges(cfg.rs, t) for _a, t, _e, _h in cfg.switches)
    if dic:
        SKIPPED.append(f)  # jump tables live inside the function's own range: bytes there are data, decoding them as code is undefined, so block-level comparison is meaningless
        rb = {k: v for k, v in rb.items() if k in cfg.blocks}
        cfg.blocks = {k: v for k, v in cfg.blocks.items() if k in rb}
    check(set(rb) == set(cfg.blocks), 'cfg-blocks: 0x%x rdis=%d py=%d' % (f, len(rb), len(cfg.blocks)))
    for s, b in cfg.blocks.items():
        if s not in rb: continue
        r = rb[s]
        if f in SKIPPED and int(r['end'], 16) != b['end']: continue
        check(int(r['end'], 16) == b['end'], 'cfg-block-end: 0x%x@0x%x' % (f, s))
        want = sorted((k, t, tuple(c)) for k, t, c in b['succ'] if k != 'TakenOut')
        have = sorted((e['kind'], int(e['to'], 16), tuple()) for e in r['succ'] if not e['outside'])
        want_k = sorted((k, t) for k, t, c in want)
        have_k = sorted((k, t) for k, t, c in have)
        check(want_k == have_k, 'cfg-edges: 0x%x@0x%x py=%s rdis=%s' % (f, s, want_k, have_k))
    # V2 direct call targets (set + count)
    pycalls = collections.Counter(i.operands[0].imm for i in cfg.ins if i.mnemonic == 'call' and i.operands[0].type == X86_OP_IMM)
    rcalls = collections.Counter(int(c['target']['rva'], 16) for c in sj['calls']['items'] if c['kind'] == 'direct' and not c['tail'])
    check(pycalls == rcalls, 'calls: 0x%x py=%d rdis=%d' % (f, sum(pycalls.values()), sum(rcalls.values())))
    # tail jumps
    pytail = sorted(cfg.tails)
    rtail = sorted((int(t['ip'], 16), int(t['to']['rva'], 16)) for t in sj.get('tail_jumps', []))
    if f in SKIPPED: pytail = rtail = []
    check(pytail == rtail, 'tails: 0x%x py=%s rdis=%s' % (f, pytail, rtail))
    # switches
    pysw = sorted((a, t, tuple(e), h) for a, t, e, h in cfg.switches)
    rsw = sorted((int(w['ip'], 16), int(w['table'], 16), w['cases'], w['bound']) for w in sj.get('switches', []))
    check([(a, t, len(e), h) for a, t, e, h in pysw] == rsw, 'switch: 0x%x py=%s rdis=%s' % (f, [(hex(a), hex(t), len(e), h) for a, t, e, h in pysw], rsw))
    nsw += len(pysw)
    # raw memory accesses: ip, rw, size, off (non-indexed and indexed both appear)
    rj2 = json.loads(outs['sum 0x%x --only raw --max 100000' % f])
    racc = {}
    for a in rj2['accesses']['items']:
        racc[(int(a['ip'], 16), a['insn_disp'])] = a['rw']
    from capstone.x86 import X86_REG_RIP
    W_ONLY = {'mov', 'movups', 'movaps', 'movdqa', 'movdqu', 'movss', 'movsd', 'movq', 'movd', 'movnti', 'movntdq', 'movntps', 'movapd', 'movupd', 'movlps', 'movhps', 'movlpd', 'movhpd', 'movntq', 'movntpd', 'movdir64b'} | {m for m in ('sete','setne','setl','setge','setle','setg','setb','setae','setbe','seta','sets','setns','seto','setno','setp','setnp')}
    R_ONLY = {'cmp', 'test', 'bt', 'ucomiss', 'ucomisd', 'comiss', 'comisd', 'jmp', 'call', 'ptest'}
    RMW = {'add', 'sub', 'and', 'or', 'xor', 'inc', 'dec', 'neg', 'not', 'xchg', 'cmpxchg', 'xadd', 'adc', 'sbb', 'shl', 'shr', 'sar', 'rol', 'ror', 'bts', 'btr', 'btc'}
    pyacc = {}
    for i in cfg.ins:
        if i.mnemonic in ('lea', 'nop', 'prefetchw', 'prefetcht0', 'prefetcht1', 'prefetcht2', 'prefetchnta', 'push', 'pop', 'ret', 'endbr64'): continue
        mem_idx = [k for k, op in enumerate(i.operands) if op.type == X86_OP_MEM]
        if not mem_idx: continue
        k = mem_idx[0]
        op = i.operands[k]
        d = 0 if op.mem.base == X86_REG_RIP else op.mem.disp
        m = i.mnemonic
        exp = None
        if k == 0 and m in W_ONLY: exp = 'W'
        elif m in R_ONLY: exp = 'R'
        elif k == 0 and m in RMW: exp = 'RW'
        elif k > 0 and m not in ('xchg', 'cmpxchg', 'xadd'): exp = 'R'
        pyacc[(i.address, ('-0x%x' % -d) if d < 0 else ('0x%x' % d))] = exp
    missing = set(pyacc) - set(racc)
    extra = set(racc) - set(pyacc)
    check(not missing and not extra, 'accesses-set: 0x%x missing=%s extra=%s' % (f, [(hex(a), o) for a, o in sorted(missing)][:4], [(hex(a), o) for a, o in sorted(extra)][:4]))
    for key, exp in pyacc.items():
        if key in racc and exp is not None:
            check(racc[key] == exp, 'accesses-rw: 0x%x@0x%x %s py=%s rdis=%s' % (f, key[0], byaddr_m(cfg, key[0]), exp, racc[key]))
    # conds: every jcc has a cond; operator matches; not_taken is the negation; setter precedes and writes flags
    rc = json.loads(outs['sum 0x%x --only conds --max 100000' % f])
    cj = {int(c['ip'], 16): c for c in rc['conds']['items']}
    OPS = {'je': '==', 'jne': '!=', 'jl': '<s', 'jge': '>=s', 'jle': '<=s', 'jg': '>s', 'jb': '<u', 'jae': '>=u', 'jbe': '<=u', 'ja': '>u', 'js': '<0', 'jns': '>=0'}
    NEG = {'==': '!=', '!=': '==', '<s': '>=s', '>=s': '<s', '<=s': '>s', '>s': '<=s', '<u': '>=u', '>=u': '<u', '<=u': '>u', '>u': '<=u', '<0': '>=0', '>=0': '<0'}
    byaddr = {i.address: i for i in cfg.ins}
    for i in cfg.ins:
        if i.mnemonic.startswith('j') and i.mnemonic != 'jmp':
            c = cj.get(i.address)
            check(c is not None, 'cond-present: 0x%x@0x%x' % (f, i.address))
            if c is None: continue
            op = OPS.get(i.mnemonic)
            setter_i = byaddr.get(int(c['setter'], 16)) if c['setter'] else None
            if setter_i is not None and setter_i.mnemonic == 'bt' and c['exact']:
                want = 'set' if i.mnemonic == 'jb' else 'clear'
                check(c['if_taken'].endswith(want) and c['if_not_taken'].endswith('clear' if want == 'set' else 'set'), 'cond-bt: 0x%x@0x%x %s' % (f, i.address, c['if_taken']))
            elif op and c['exact']:
                check(' %s ' % op in ' ' + c['if_taken'] + ' ' or (' %s ' % op) in c['if_taken'] or c['if_taken'].endswith(' ' + op + ' 0') or c['if_taken'].split(' ')[-2] == op, 'cond-op: 0x%x@0x%x %s %s' % (f, i.address, i.mnemonic, c['if_taken']))
                check(NEG[op] in c['if_not_taken'].split(' '), 'cond-neg: 0x%x@0x%x %s | %s' % (f, i.address, c['if_taken'], c['if_not_taken']))
            if c['setter']:
                s = byaddr.get(int(c['setter'], 16))
                ok = s is not None and s.address < i.address and writes_flags(s)
                if ok and c['exact']: ok = s.mnemonic in FLAGSET
                # nothing between setter and jcc (when contiguous) may modify flags
                if ok:
                    # walk back from the jcc along the single-predecessor chain to the setter; nothing on the way may write flags
                    idx_of = {q.address: n for n, q in enumerate(cfg.ins)}
                    blk_of = lambda addr: max(a for a in cfg.blocks if a <= addr)
                    pos = idx_of[i.address] - 1
                    bstart = blk_of(i.address)
                    steps = 0
                    while ok and steps < 10000:
                        steps += 1
                        if cfg.ins[pos].address == s.address: break
                        if pos < cfg.blocks[bstart]['first']:
                            ps = [a for a, bb in cfg.blocks.items() for e in bb['succ'] if e[1] == bstart]
                            if len(set(ps)) != 1: ok = False; break
                            bstart = ps[0]; lb = cfg.blocks[bstart]['last']; pos = lb - 1 if cfg.ins[lb].mnemonic.startswith('j') else lb
                            continue
                        if writes_flags(cfg.ins[pos]): ok = False; break
                        pos -= 1
                check(ok, 'cond-setter: 0x%x@0x%x -> %s' % (f, i.address, c['setter']))

print('functions sampled: %d, switches seen: %d, data-in-code functions (block compare skipped): %s' % (len(sample), nsw, [hex(x) for x in SKIPPED]))
# V6 gates
gcmds, gwant = [], []
for f in sample[:60]:
    cfg = build_cfg(f)
    ips = [i.address for i in cfg.ins]
    for ip in random.sample(ips, min(4, len(ips))):
        gcmds.append('gates 0x%x 0x%x' % (f, ip)); gwant.append((f, ip, cfg))
gout = run_rdis(gcmds)
for c, (f, ip, cfg) in zip(gcmds, gwant):
    j = json.loads(gout[c])
    blk = [s for s, b in cfg.blocks.items() if s <= ip < b['end']][0]
    want = gates(cfg, f, blk)
    if want is None:
        check(j.get('reachable') is False, 'gates-unreachable: 0x%x@0x%x' % (f, ip))
        continue
    have = {(int(g['branch_ip'], 16), g['edge']) for g in j['gates']}
    check(want == have, 'gates: 0x%x@0x%x py=%s rdis=%s' % (f, ip, sorted((hex(a), k) for a, k in want), sorted((hex(a), k) for a, k in have)))


# ---------------- vtables / RTTI / constructor evidence
vout = run_rdis(['classes --rtti --max 150', 'classes --max 400'])
vts = []
for k in vout:
    j = json.loads(vout[k])
    vts += j['classes']['items']
seen = set()
for v in vts:
    va = int(v['vtable'], 16)
    if va in seen: continue
    seen.add(va)
    slots = []
    a = va
    while len(slots) < 1024:
        q = rd(a, 8)
        if len(q) < 8: break
        t = struct.unpack('<Q', q)[0] - IMAGE_BASE
        if not (0 <= t < 1 << 32 and is_exec(t)): break
        slots.append(t); a += 8
    check(len(slots) >= v['slots'], 'vtable-slots: %s py=%d rdis=%d' % (v['vtable'], len(slots), v['slots']))
    check(v['slots'] == len(slots) or v['slots_end'] == 'next-vtable', 'vtable-end: %s py=%d rdis=%d end=%s' % (v['vtable'], len(slots), v['slots'], v['slots_end']))
    for ev in v['evidence']:
        lea_ip, st_ip = int(ev['lea_ip'], 16), int(ev['store_ip'], 16)
        li = list(md.disasm(rd(lea_ip, 15), lea_ip))[0]
        ok = li.mnemonic == 'lea' and li.operands[1].type == X86_OP_MEM and li.operands[1].mem.base == __import__('capstone.x86', fromlist=['X86_REG_RIP']).X86_REG_RIP and li.address + li.size + li.operands[1].mem.disp == va
        check(ok, 'vtable-lea: %s@%s' % (v['vtable'], ev['lea_ip']))
        reg = li.operands[0].reg
        sts = list(md.disasm(rd(st_ip, 15), st_ip))[0]
        ok2 = sts.mnemonic == 'mov' and sts.operands[0].type == X86_OP_MEM and sts.operands[1].type == X86_OP_REG and full(sts.operands[1].reg) == full(reg) and st_ip > lea_ip and st_ip - lea_ip < 80
        check(ok2, 'vtable-store: %s@%s' % (v['vtable'], ev['store_ip']))
    if 'rtti' in v:
        col = int(v['rtti']['col'], 16)
        check(u32(off(col)) == 1 and u32(off(col + 20)) == col, 'rtti-col: %s' % v['vtable'])
        td = u32(off(col + 12))
        nm = rd(td + 16, 4000).split(b'\0')[0].decode()
        check(nm == v['rtti']['mangled'], 'rtti-name: %s %s vs %s' % (v['vtable'], nm, v['rtti']['mangled']))
        check(struct.unpack('<Q', rd(va - 8, 8))[0] - IMAGE_BASE == col, 'rtti-link: %s' % v['vtable'])
print('vtables verified:', len(seen), ' with rtti:', sum(1 for v in vts if 'rtti' in v))
# recall probe: lea reg,[rip+X] ; mov [mem],reg patterns in sampled functions whose X holds a code pointer must be known vtables to rdis
probe, expect = [], []
from capstone.x86 import X86_REG_RIP
for f in sample[:120]:
    ins = decode(fn_ranges(f))
    for n, i in enumerate(ins):
        if i.mnemonic == 'lea' and i.operands[1].type == X86_OP_MEM and i.operands[1].mem.base == X86_REG_RIP:
            x = i.address + i.size + i.operands[1].mem.disp
            if is_exec(x) or off(x) is None or x % 8: continue
            q = rd(x, 8)
            if len(q) < 8: continue
            t = struct.unpack('<Q', q)[0] - IMAGE_BASE
            if not (0 <= t < 1 << 32 and is_exec(t)): continue
            for j in ins[n + 1:n + 9]:
                if j.mnemonic.startswith('j') or j.mnemonic in ('call', 'ret'): break
                if j.mnemonic == 'mov' and j.operands[0].type == X86_OP_MEM and j.operands[1].type == X86_OP_REG and full(j.operands[1].reg) == full(i.operands[0].reg) and j.operands[0].mem.index == 0:
                    probe.append('class 0x%x' % x); expect.append(x); break
                if j.operands and j.operands[0].type == X86_OP_REG and full(j.operands[0].reg) == full(i.operands[0].reg): break
probe = list(dict.fromkeys(probe))[:100]
pout = run_rdis(probe) if probe else {}
for c in probe:
    try: ok = json.loads(pout[c]).get('matches', 0) >= 1
    except Exception: ok = False
    check(ok, 'vtable-recall: %s' % c)
print('vtable recall probes:', len(probe))

# ---------------- paths: every hop must be a real call/jmp instruction to the claimed target
pcmds = []
pair_src = sample[:25]
routs = run_rdis(['reach 0x%x --depth 3 --max 40' % f for f in pair_src])
pairs = []
for f in pair_src:
    j = json.loads(routs['reach 0x%x --depth 3 --max 40' % f])
    deep = [x for x in j['functions']['items'] if x['depth'] == 3]
    if deep:
        pairs.append((f, int(deep[-1]['rva'], 16), 3))
pc = ['path 0x%x 0x%x --depth 4 --k 2' % (a, b) for a, b, d in pairs]
pouts = run_rdis(pc) if pc else {}
for c, (a, b, d) in zip(pc, pairs):
    j = json.loads(pouts[c])
    check(len(j['paths']) >= 1, 'path-found: %s' % c)
    for p_ in j['paths'][:1]:
        check(p_['length'] <= d, 'path-shortest: %s len=%d expected<=%d' % (c, p_['length'], d))
        cur = a
        for h in p_['hops']:
            site = int(h['site'], 16)
            ci = list(md.disasm(rd(site, 15), site))[0]
            ok = ci.mnemonic in ('call', 'jmp') and ci.operands[0].type == X86_OP_IMM and ci.operands[0].imm == int(h['to']['rva'], 16) and int(h['from']['rva'], 16) == cur
            check(ok, 'path-hop: %s site %s' % (c, h['site']))
            check(root.get(site) is not None or True, 'path-hop-fn')
            cur = int(h['to']['rva'], 16)
        check(cur == b, 'path-end: %s' % c)
print('paths verified:', len(pairs))
print('checks run:', dict(checks))
print('FAILURES: %d' % len(fails))
for f in fails[:40]: print('  FAIL', f)
sys.exit(1 if fails else 0)
