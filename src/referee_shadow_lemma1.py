from fractions import Fraction as F
import random

# Engine's construction, generalised: total mass > C, t = C/2 groups, each in (4/3, 2].
def engine_construct(xs, C=64, t=32, lo=F(4,3), hi=F(2), big=F(2,3)):
    idx = list(range(len(xs)))
    large = [i for i in idx if xs[i] > big]
    small = [i for i in idx if xs[i] <= big]
    groups = []
    if len(large) >= 2*t:
        sel = large[:2*t]
        for j in range(t):
            groups.append([sel[2*j], sel[2*j+1]])
        return groups
    l = len(large)
    s = l//2
    for j in range(s):
        groups.append([large[2*j], large[2*j+1]])
    leftover_large = large[2*s:]      # 0 or 1 item
    pool = leftover_large + small     # leftover large first
    r = t - s
    pos = 0
    for j in range(r):
        g = []; tot = F(0)
        while tot <= lo:
            if pos >= len(pool):
                return None           # construction failed
            g.append(pool[pos]); tot += xs[pool[pos]]; pos += 1
        groups.append(g)
    return groups

# independent greedy: sort descending, fill each group until > 4/3
def indep_greedy(xs, C=64, t=32, lo=F(4,3), hi=F(2)):
    order = sorted(range(len(xs)), key=lambda i: -xs[i])
    groups = []; pos = 0
    for j in range(t):
        g=[]; tot=F(0)
        while tot <= lo:
            if pos >= len(order): return None
            g.append(order[pos]); tot += xs[order[pos]]; pos += 1
        groups.append(g)
    return groups

def check(xs, groups, t=32, lo=F(4,3), hi=F(2)):
    if groups is None: return "NO-GROUPS"
    if len(groups) != t: return "WRONG-COUNT %d"%len(groups)
    seen=set()
    for g in groups:
        for i in g:
            if i in seen: return "OVERLAP"
            seen.add(i)
        tot = sum(xs[i] for i in g)
        if not (tot > lo and tot <= hi): return "MASS %s"%tot
    return "OK"

random.seed(20260904)
fails = {"engine":0, "greedy":0}
first_fail = {}
N_TESTS = 4000
for trial in range(N_TESTS):
    mode = trial % 8
    n = random.randint(65, 200)
    if mode==0:   xs=[F(random.randint(1,1000),1000) for _ in range(n)]
    elif mode==1: xs=[F(random.randint(667,1000),1000) for _ in range(n)]   # all "large"
    elif mode==2: xs=[F(random.randint(1,667),1000) for _ in range(n)]      # all "small"
    elif mode==3: xs=[F(random.randint(1,50),1000) for _ in range(n)]       # tiny
    elif mode==4: xs=[F(1) for _ in range(n)]
    elif mode==5: xs=[F(2,3)+F(1,10**6) for _ in range(n)]                  # just above 2/3
    elif mode==6: xs=[F(2,3) for _ in range(n)]                             # exactly 2/3 (small)
    else:
        nl = random.randint(0,63)
        xs=[F(random.randint(667,1000),1000) for _ in range(nl)]+[F(random.randint(1,667),1000) for _ in range(n)]
        random.shuffle(xs)
    tot = sum(xs)
    if tot <= 64:
        # top up with items of size 1 until strictly > 64
        while sum(xs) <= 64: xs.append(F(1))
    random.shuffle(xs)
    for name, fn in (("engine", engine_construct), ("greedy", indep_greedy)):
        res = check(xs, fn(xs))
        if res != "OK":
            fails[name]+=1
            if name not in first_fail: first_fail[name]=(mode,res,len(xs),float(sum(xs)))
print("tests", N_TESTS, "failures", fails)
print("first failures", first_fail)
