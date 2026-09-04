# 结论

本轮得到的最强严格结果是：

1. **T2 被明确反驳。** 原始随机分割误差估计 \((RP_{64})\) 在一个极小、完全位于 sparse core 内的例子上失败，差额恰为 \(1/4096\)。

2. **“只使用所有合取计数的 \(0/1\) 误差界”不足以推出任何绝对阈值。** 阶 \(q\) 射影平面给出一族显式抽象对手：每个非空合取的计数只增加 \(0\) 或 \(1\)，平均质量趋于 \(1\)，但阈值 \(q\) 的左侧仍比阈值 \(1\) 的右侧大 \(1\)。对 \(q=67\)，它直接击穿抽象版 \(C=64\)。

3. **这个射影平面对手不能实现为真实素数幂 floor 表。** 障碍可精确定位到二阶：其单点计数会迫使任意两个真实原子模数之积大于 \(m\)，但设计要求每一对恰好共现一次。这说明真正缺少的算术输入正是

   $$
   d_{A\cup B}=\operatorname{lcm}(d_A,d_B),
   $$

   特别是不同素数上的乘法关系，而不只是

   $$
   N_I(d)\in\{\lfloor m/d\rfloor,\lfloor m/d\rfloor+1\}.
   $$

4. **\((SC_{64})\) 在一个巨大范围内无条件成立：**

   $$
   m<P_{65}:=\prod_{i=1}^{65}p_i
   =61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210.
   $$

   即约 \(6.1077\cdot10^{127}\)。原因是 \(S_0(k)\le \omega(k)\le64\)，所以左侧恒为零。

5. 对其余范围，得到全阶、完全算术化的因子矩界

   $$
   \sum_{k\le m}(S_0(k)-64)^+
   \le \frac{mH_{64}^{65}}{65!}
   <6.239\cdot10^{-90}m,
   $$

   以及一个精确的 Hall/容量传输归约。尚缺的是证明该传输在真实素数幂 floor 系统中总能以绝对容量常数完成。

因此，本轮没有合法推出全体 \(m\) 的 T1，也没有合法推出 \(g(n)\le 81n\) 或 \(18n\)；但 T2 已被彻底排除，T3 的“纯计数版”已被彻底排除，而剩余问题被压缩到了真实乘法 floor 表的一个明确容量命题。

---

## Lemma 1 — 随机分割系数公式

**状态：PROVED**

先只考虑单位原子。令

$$
h(t):=(t-1)^+,\qquad t\in\mathbf Z_{\ge0}.
$$

它在 Boolean cube 上、大小为 \(j\) 的集合对应的 Möbius 系数为

$$
\mu_j=\sum_{i=0}^j(-1)^{j-i}\binom ji(i-1)^+=(-1)^j,\qquad j\ge2.
$$

证明很短。对 \(j\ge2\)，函数 \(i-1\) 的 \(j\) 阶有限差分为零；而

$$
(i-1)^+=(i-1)+\mathbf 1_{\{i=0\}},
$$

所以只剩下 \(i=0\) 的贡献 \((-1)^j\)。

现在把原子独立均匀分进 \(r\) 个颜色块，并对各块取 \(h\) 后求和。一个含 \(j\) 个原子的 Möbius 单项式只有在这 \(j\) 个原子同色时出现，其概率为

$$
r\cdot r^{-j}=r^{1-j}.
$$

因此随机分割聚合后的系数为

$$
\gamma_A=(-1)^{|A|}r^{1-|A|},\qquad |A|\ge2.
$$

特别地，三原子系数为

$$
\gamma_{\{1,2,3\}}=-\frac1{r^2}.
$$

---

## Lemma 2 — \((RP_{64})\) 的显式反例

**状态：REFUTED**

取

$$
m=4097,\qquad z_2=z_3=z_5=1,
$$

其余权重为零。

此时只有三个单位原子 \(2,3,5\)，并且

$$
\frac m{64}=64+\frac1{64},
$$

所以 \(2,3,5\) 以及负三阶系数对应的模数

$$
2\cdot3\cdot5=30
$$

都严格位于 \(m/64\) 以下。稀疏参数为

$$
H_{64}=\frac12+\frac13+\frac15=\frac{31}{30}<\frac{17}{16}.
$$

由 Lemma 1，随机 \(64\)-分割证书有一个负系数

$$
-\frac1{64^2}=-\frac1{4096}.
$$

由于只有三个素数，

$$
S(k)\le3<64
$$

对所有 \(k\) 成立，故

$$
\sum_{k\le m}\min\bigl((S(k)-64)^+,64\bigr)=0.
$$

另一方面

$$
E_{64}=\frac1{4096}>0.
$$

所以

$$
E_{64}\le
\sum_{k\le m}\min\bigl((S(k)-64)^+,64\bigr)
$$

是假的。

这不是边界模数被截掉造成的假反例：负模数 \(30\) 本身满足 \(30<m/64\)。

因此 **T2 按题面写法被严格反驳**。

---

## Lemma 3 — 更强的随机分割诊断例

**状态：PROVED；用于击破修补方案**

取

$$
m=10^6,\qquad p_1=1009,\ p_2=1013,\ p_3=1019,
$$

均取单位权重。则

$$
p_i\le \frac m{64}=15625,
$$

但

$$
1009\cdot1013=1022117>m,
$$

另外两对之积也都大于 \(m\)。

故在 \(K=[1,m]\) 中没有任何数同时被两个选定素数整除，于是：

$$
S(k)\le1,\qquad
G_{64}(S(k))=0,\qquad
(S(k)-C)^+=0
$$

对任意 \(C\ge1\) 成立。

但随机分割形式中仍存在负三阶系数 \(-1/4096\)。因此甚至不能把原始 \(E_{64}\) 普遍改成

$$
E_{64}\le
\sum_K\bigl(G_{64}(S(k))-(S(k)-C)^+\bigr).
$$

这个例子精确说明问题所在：若某个右端整数同时含三个素数，则三阶负边界误差和三个二阶正边界误差是在**同一个整数上同时出现并相互抵消**的。逐模数支付每个负系数，会丢失这种边界相干性。

---

## Lemma 4 — 极稀疏情形下 \((TH_1)\) 仍然失败

**状态：PROVED；adversarial test**

取

$$
m=11021,\qquad P=\{101,103,107\},
$$

均为单位权重。三对乘积为

$$
101\cdot103=10403,\quad
101\cdot107=10807,\quad
103\cdot107=11021.
$$

它们均位于 \((m/2,m]\)。同时

$$
H=\frac1{101}+\frac1{103}+\frac1{107}
=\frac{32231}{1113121}<\frac1{32}.
$$

在 \(K=[1,m]\) 中，每一个二素数乘积恰出现一次，三素数乘积大于 \(m\)。故

$$
\sum_{k\le m}(S(k)-1)^+=3.
$$

令

$$
L=101\cdot103\cdot107=1113121
$$

并取以 \(L\) 为中心、长度 \(m\) 的区间，即偏移量

$$
-5510,-5509,\ldots,0,\ldots,5509,5510.
$$

因为每个选定素数整除 \(L\)，

$$
p\mid L+t\iff p\mid t.
$$

当 \(0<|t|\le5510\) 时，\(t\) 小于任意一对素数之积，所以至多含一个选定素数；在 \(t=0\) 处则同时含三个。因此

$$
\sum_{b\in I}(S(b)-1)^+=3-1=2.
$$

所以即使 \(H<1/32\)，也有

$$
\sum_K(S-1)^+=3>2=\sum_I(S-1)^+.
$$

这击破了如下潜在 T4 基础命题：

> “把素数分成若干个极小 harmonic-mass 的块后，每块满足 \((TH_1)\)。”

小 harmonic mass 本身不够；仍须利用高阈值提供的层级余量。

---

# 抽象两侧计数对手

## Lemma 5 — Fano 平面的“每个合取只增至多一格”反例

**状态：PROVED**

令点集为 Fano 平面的七个点，七条线均含三个点，每个点在三条线上，每一对点恰属于一条线。

构造两个各有 \(15\) 行的 pattern multiset：

$$
\mu:
\quad
8\text{ 个空集}
\quad+\quad
7\text{ 条 Fano 线各一次};
$$

$$
\nu:
\quad
每个单点各两次
\quad+\quad
1\text{ 个全七点集}.
$$

对任意非空点集 \(A\)，令

$$
N_\mu(A)=\#\{B\in\mu:A\subseteq B\},
\qquad
N_\nu(A)=\#\{B\in\nu:A\subseteq B\}.
$$

逐阶检查：

* \(|A|=1\)：两边都为 \(3\)；
* \(|A|=2\)：两边都为 \(1\)；
* \(|A|\ge3\)：\(N_\mu(A)\in\{0,1\}\)，而 \(N_\nu(A)=1\)。

因此

$$
N_\nu(A)-N_\mu(A)\in\{0,1\}
$$

对每个非空 \(A\) 成立。

但在单位权重下，

$$
\sum_{B\in\mu}(|B|-2)^+
=7,
$$

而

$$
\sum_{B\in\nu}(|B|-1)^+
=7-1=6.
$$

所以即使**每一个非空合取计数只增加零格或一格**，阈值 \(2\) 仍可能失败。

这也解释了为什么题面的 M2 必须使用真实的
\(\lfloor m/d_A\rfloor\) 乘法表，而不只是抽象的 one-step upper-orthant 条件。

---

## Lemma 6 — 任意阈值的射影平面对手

**状态：PROVED**

令 \(q\) 为素数，取阶 \(q\) 的射影平面。其点数、线数均为

$$
v=q^2+q+1,
$$

每条线有 \(q+1\) 个点，每个点在 \(q+1\) 条线上，任意两点唯一确定一条线。

可显式取：

* 仿射点 \((x,y)\in\mathbf F_q^2\)；
* \(q+1\) 个无穷远点；
* 直线 \(y=ax+b\)、竖直线 \(x=c\)、无穷远线。

令

$$
m=qv+1.
$$

构造：

$$
\mu:
\quad
每条线一次
\quad+\quad
((q-1)v+1)\text{ 个空行};
$$

$$
\nu:
\quad
每个单点各 }q\text{ 次}
\quad+\quad
1\text{ 个全点集}.
$$

两者都有 \(m\) 行。

对非空 \(A\)：

1. 若 \(|A|=1\)，两边计数均为 \(q+1\)；
2. 若 \(|A|=2\)，两边计数均为 \(1\)；
3. 若 \(|A|\ge3\)，\(\mu\) 中 \(A\) 至多位于一条线，故计数为 \(0\) 或 \(1\)；\(\nu\) 中计数恒为 \(1\)。

所以

$$
N_\nu(A)-N_\mu(A)\in\{0,1\}
\qquad(A\ne\varnothing).
$$

单位权重下，在阈值 \(C=q\)：

$$
\sum_{\mu}(|B|-q)^+
=v,
$$

因为每条线大小为 \(q+1\)；而

$$
\sum_{\nu}(|B|-1)^+
=v-1,
$$

因为只有全点行有贡献。

于是

$$
\sum_{\mu}(|B|-q)^+
=
\sum_{\nu}(|B|-1)^+ +1.
$$

更一般地，对任意固定 \(C\)，取素数 \(q>C\)，则

$$
\sum_\mu(|B|-C)^+
-
\sum_\nu(|B|-1)^+
=
v(q-C)+1>0.
$$

因此：

> 不存在由“所有非空合取计数增加 \(0\) 或 \(1\)”单独推出的绝对阈值 \(C\)。

此外，\(\mu\) 的平均质量为

$$
\overline S_\mu
=\frac{v(q+1)}{qv+1}
<1+\frac1q.
$$

当 \(q\ge17\) 时，

$$
\overline S_\mu<\frac{17}{16}.
$$

所以该对手甚至通过了 A1 的“平均质量约为 \(1\)”诊断。

### 具体的 \(C=64\) 实例

取 \(q=67\)。则

$$
v=4557,\qquad m=305320,
\qquad \overline S_\mu=\frac{4557}{4490}<\frac{17}{16}.
$$

在阈值 \(64\)：

$$
\text{LHS}=4557(68-64)=18228,
$$

而

$$
\text{RHS}=4556.
$$

抽象差额为

$$
18228-4556=13672.
$$

---

## Lemma 7 — 射影平面对手不可能是实际 prime-power floor 表

**状态：PROVED**

这是区分 Lemma 6 与题面 T3 的关键。

射影平面基准 \(\mu\) 中，每个单点的计数为 \(q+1\)。若它来自真实的

$$
K=[1,m]
$$

和单位素数原子，原子模数记为 \(d_i\)，则必须有

$$
\left\lfloor\frac m{d_i}\right\rfloor=q+1.
$$

因此

$$
d_i>\frac m{q+2}.
$$

对 \(q\ge3\)，

$$
m=q(q^2+q+1)+1=q^3+q^2+q+1>(q+2)^2,
$$

因为

$$
m-(q+2)^2=q^3-3q-3>0.
$$

故任意两个不同素数基的原子满足

$$
d_i d_j>
\frac{m^2}{(q+2)^2}>m.
$$

于是

$$
\left\lfloor\frac m{d_i d_j}\right\rfloor=0.
$$

但射影平面基准要求每一对点恰共现一次，即二阶计数为 \(1\)。矛盾。

所以 Lemma 6 严格证明的是：

> **T3-counting-only：成立。**
> 仅靠每个合取计数的上下两侧一格界，以及稀疏平均质量，不能推出绝对阈值。

但它没有达到题面要求的：

> **T3-floor-realizable：尚未证明。**

缺失条件已经精确识别为真实模数的乘法／lcm 一致性。

---

# 对真实 sparse core 的无条件结果

## Lemma 8 — \(65\) 个素数的 primorial 屏障

**状态：PROVED**

对每个素数 \(p\)，

$$
a_p(k):=\sum_j\alpha_{p,j}\mathbf1_{p^j\mid k}
\le\sum_j\alpha_{p,j}\le1.
$$

因此

$$
S_0(k)=\sum_p a_p(k)\le \omega(k),
$$

其中 \(\omega(k)\) 是不同素因子数。

若 \(S_0(k)>64\)，则

$$
\omega(k)\ge65.
$$

任何含至少 \(65\) 个不同素因子的整数都至少为前 \(65\) 个素数之积：

$$
P_{65}:=\prod_{i=1}^{65}p_i.
$$

其中 \(p_{65}=313\)，并且

$$
\begin{aligned}
P_{65}
={}&61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210.
\end{aligned}
$$

因此，当

$$
m<P_{65}
$$

时，对每个 \(k\le m\) 都有 \(S_0(k)\le64\)，从而

$$
\sum_{k\le m}(S_0(k)-64)^+=0.
$$

于是对任意区间 \(I\)，

$$
\sum_{k\le m}(S_0(k)-64)^+
\le
\sum_{b\in I}(S_0(b)-1)^+.
$$

即：

$$
\boxed{(SC_{64})\text{ 对所有 }m<P_{65}\text{ 无条件成立。}}
$$

这把真正可能出问题的 sparse-core 范围推到了约

$$
6.1077\cdot10^{127}
$$

以上。

---

## Lemma 9 — 全阶因子矩不等式

**状态：PROVED**

令

$$
a_p(n):=\sum_{j:p^j\le m/64}\alpha_{p,j}\mathbf1_{p^j\mid n},
\qquad
S_0(n)=\sum_p a_p(n),
$$

并定义每个素数的 harmonic mass

$$
h_p:=\sum_{j:p^j\le m/64}\frac{\alpha_{p,j}}{p^j},
\qquad
H:=\sum_p h_p=H_{64}(m,z).
$$

对非负向量 \((u_p)\)，记

$$
e_\ell(u):=\sum_{p_1<\cdots<p_\ell}
u_{p_1}\cdots u_{p_\ell}.
$$

则对每个整数 \(\ell\ge1\)：

$$
\boxed{
\sum_{k\le m}e_\ell\bigl((a_p(k))_p\bigr)
\le m\,e_\ell((h_p)_p)
\le \frac{mH^\ell}{\ell!}.
}
$$

### 证明

展开左侧：

$$
\begin{aligned}
\sum_{k\le m}e_\ell(a(k))
&=
\sum_{p_1<\cdots<p_\ell}
\sum_{j_1,\ldots,j_\ell}
\alpha_{p_1,j_1}\cdots\alpha_{p_\ell,j_\ell}
\left\lfloor
\frac m{p_1^{j_1}\cdots p_\ell^{j_\ell}}
\right\rfloor\\
&\le
m\sum_{p_1<\cdots<p_\ell}
\prod_{i=1}^{\ell}
\left(
\sum_{j_i}\frac{\alpha_{p_i,j_i}}{p_i^{j_i}}
\right)\\
&=m\,e_\ell(h).
\end{aligned}
$$

不同 \(p_i\) 使模数相乘，这是此处不可替代的算术输入。

最后，

$$
H^\ell
=
\left(\sum_p h_p\right)^\ell
\ge
\ell!\sum_{p_1<\cdots<p_\ell}h_{p_1}\cdots h_{p_\ell}
=\ell!e_\ell(h).
$$

同样，由于任意长度 \(m\) 的区间中，模数 \(d\) 的倍数个数不小于 \(\lfloor m/d\rfloor\)，还有

$$
\sum_{b\in I}e_\ell(a(b))
\ge
\sum_{k\le m}e_\ell(a(k)).
$$

所以所有不同素数方向的正因子矩在 \(I\) 中都不会减小。

---

## Lemma 10 — 高阈值 hinge 被第 \(C+1\) 个初等对称式控制

**状态：PROVED**

设

$$
0\le u_i\le1,\qquad s=\sum_i u_i,
$$

且 \(C\) 为非负整数，则

$$
\boxed{(s-C)^+\le e_{C+1}(u).}
$$

### 证明

固定总和 \(s\)。如果两个坐标 \(x,y\) 都严格位于 \((0,1)\)，固定 \(x+y\) 后，

$$
e_r(x,y,u')
=
xy\,e_{r-2}(u')
+(x+y)e_{r-1}(u')
+e_r(u').
$$

由于 \(e_{r-2}(u')\ge0\)，为了最小化 \(e_r\)，可把 \(x,y\) 中至少一个推到 \(0\) 或 \(1\)。反复进行，极小值在至多一个分数坐标处取得。

写

$$
s=q+\theta,\qquad q=\lfloor s\rfloor,\quad0\le\theta<1.
$$

于是

$$
e_{C+1}(u)
\ge
\binom q{C+1}+\theta\binom qC.
$$

若 \(q<C\)，左侧 hinge 为零；若 \(q=C\)，右边等于

$$
\theta=s-C.
$$

若 \(q\ge C+1\)，则

$$
\binom q{C+1}\ge q-C,\qquad
\binom qC\ge1,
$$

故

$$
e_{C+1}(u)\ge q-C+\theta=s-C.
$$

---

## Corollary 11 — sparse-core 左尾的显式密度界

**状态：PROVED**

由 Lemma 9 和 Lemma 10，在 \(C=64\) 时：

$$
\begin{aligned}
L_{64}
&:=
\sum_{k\le m}(S_0(k)-64)^+\\
&\le
\sum_{k\le m}e_{65}\bigl((a_p(k))_p\bigr)\\
&\le
\frac{mH^{65}}{65!}.
\end{aligned}
$$

当 \(H<17/16\) 时，

$$
\boxed{
L_{64}
<
\frac{m(17/16)^{65}}{65!}
<
6.239\cdot10^{-90}m.
}
$$

因此，任何仍可能存在的 \((SC_{64})\) 反例，其左侧密度都小于 \(6.239\cdot10^{-90}\)。

---

## Lemma 12 — 单个高点强迫右侧至少 \(63\)

**状态：PROVED**

若某个 \(k\le m\) 满足

$$
S_0(k)>64,
$$

则任意长度 \(m\) 的区间 \(I\) 中至少有一个 \(k\) 的倍数 \(b\)，因为

$$
\#\{b\in I:k\mid b\}\ge\left\lfloor\frac mk\right\rfloor\ge1.
$$

对所有保留原子 \(p^j\)，

$$
p^j\mid k\implies p^j\mid b,
$$

所以

$$
S_0(b)\ge S_0(k)>64.
$$

于是

$$
\sum_{b\in I}(S_0(b)-1)^+>63.
$$

因此若 \(L_{64}>0\)，则右侧 \(R\) 满足

$$
R>63.
$$

若存在反例 \(R<L_{64}\)，结合 Corollary 11，

$$
63<R<L_{64}<6.239\cdot10^{-90}m,
$$

故至少

$$
m>
63\cdot65!\left(\frac{16}{17}\right)^{65}
\approx1.0099\cdot10^{91}.
$$

Lemma 8 给出的 \(m\ge P_{65}\approx6.1077\cdot10^{127}\) 更强。

所以任何剩余反例必须同时满足：

$$
\boxed{
m\ge P_{65},\qquad
63<R<L_{64}<6.239\cdot10^{-90}m.
}
$$

---

# T4：容量传输归约

## Lemma 13 — atomwise capacitated transport 足以推出 \((TH_C)\)

**状态：PROVED REDUCTION**

令原子集合记作 \(\mathcal A\)，原子 \(a=(p,j)\) 的模数为

$$
q_a=p^j,
$$

权重为 \(\alpha_a\)。

固定任意

$$
t_k\in[0,1]\qquad(k\le m).
$$

假设总能找到

$$
\lambda_b\in[0,1]\qquad(b\in I)
$$

满足：

$$
\sum_{\substack{b\in I\\q_a\mid b}}\lambda_b
\ge
\sum_{\substack{k\le m\\q_a\mid k}}t_k
\qquad\text{对每个原子 }a,
\tag{Coverage}
$$

以及

$$
\sum_{b\in I}\lambda_b
\le C\sum_{k\le m}t_k.
\tag{Cost}
$$

则 \((TH_C)\) 成立。

### 证明

对 \(0\le\lambda\le1\)，

$$
(u-1)^+\ge\lambda(u-1).
$$

故

$$
\begin{aligned}
\sum_{b\in I}(S(b)-1)^+
&\ge
\sum_{b\in I}\lambda_b(S(b)-1)\\
&=
\sum_a\alpha_a
\sum_{\substack{b\in I\\q_a\mid b}}\lambda_b
-\sum_b\lambda_b\\
&\ge
\sum_a\alpha_a
\sum_{\substack{k\le m\\q_a\mid k}}t_k
-C\sum_k t_k\\
&=
\sum_{k\le m}t_k(S(k)-C).
\end{aligned}
$$

最后利用可分离的 hinge 对偶公式

$$
\sum_{k\le m}(S(k)-C)^+
=
\max_{0\le t_k\le1}
\sum_{k\le m}t_k(S(k)-C).
$$

因此 Coverage+Cost 对每个 \(t\) 成立，即推出 \((TH_C)\)。

### 这一定理精确隔离了剩余困难

对单个原子 \(q_a\)，因为

$$
\#\{k\le m:q_a\mid k\}
=
\left\lfloor\frac m{q_a}\right\rfloor
\le
\#\{b\in I:q_a\mid b\},
$$

每一个 Coverage 约束单独看都可满足。

困难完全来自不同原子的覆盖集合在 \(I\) 中发生碰撞。也就是说，剩余问题可以写成：

> 真实 prime-power multiples set system 是否有绝对常数的分数容量膨胀界？

这是一个明确的 Hall 型命题，不再是模糊的“需要更好的证书”。

Lemma 5–7 表明：对任意抽象 set system，该命题为假；真实模数乘法必须进入证明。

---

# 各目标的最终状态

### T1 — \((SC_r)\) 全体 \(m\)

**状态：PARTIAL PROVED**

严格得到

$$
(SC_{64})\quad\text{对所有 }m<P_{65}
$$

成立，并且任何剩余反例必须满足

$$
m\ge P_{65},\qquad
63<R<L<6.239\cdot10^{-90}m.
$$

尚未得到 \(m\ge P_{65}\) 的 all-\(m\) 证明。

### T2 — \((RP_{64})\)

**状态：REFUTED**

显式反例：

$$
m=4097,\quad z_2=z_3=z_5=1,
\quad H_{64}=31/30,
$$

其中

$$
E_{64}=1/4096,\qquad
\sum_K\min((S-64)^+,64)=0.
$$

### T3 — 抽象对手

**状态：两部分**

* **T3-counting-only：PROVED。**
  射影平面族表明，即使每个非空合取计数只增加 \(0\) 或 \(1\)，并且平均质量趋于 \(1\)，仍不存在绝对阈值。

* **T3-floor-realizable：UNPROVED。**
  射影平面族被 Lemma 7 的真实 floor 乘法约束排除。尚未构造满足真实

  $$
  N_K(A)=\left\lfloor\frac m{\prod_{p\in A}p^{j_p}}\right\rfloor
  $$

  的同类对手。

### T4 — 不经 sparse certificate 的归约

**状态：PROVED REDUCTION**

Lemma 13 给出了一个精确的 atomwise capacitated transport 充分条件。未证明项仅剩该 transport 的绝对成本界。

### P3 dense branch

**状态：CONDITIONAL**

本轮没有独立重构 P3 的 \(H_{64}\ge17/16\Rightarrow(TH_{65})\) 证明，因此没有把它作为无条件引理使用，也没有据此声称得到 \(g(n)\) 的线性上界。

---

# Lean 形式化需要的内容

1. **随机分割反例。**
   在 `Fin 3` 上枚举 Boolean Möbius 变换，证明三阶系数为 \(-1\)，再以 `norm_num` 验证

   $$
   \frac{31}{30}<\frac{17}{16},
   \qquad
   \frac1{4096}>0.
   $$

2. **Fano 反例。**
   可直接把七条线写成七个 `Finset (Fin 7)`，用 `native_decide` 验证：

   * 每点度数 \(3\)；
   * 每对点唯一共线；
   * 所有 \(2^7\) 个集合的 upper-count discrepancy 属于 \(\{0,1\}\)。

3. **一般射影平面族。**
   对素数 \(q\) 使用 `ZMod q`：

   * 仿射线 `y = a*x+b`；
   * 竖直线；
   * 无穷远线。

   只需形式化“每点 \(q+1\) 条线、每对点唯一一线”，其余 upper-count 结论立即得到。

4. **floor 不相容。**
   完全是整数不等式：

   $$
   \lfloor m/d_i\rfloor=q+1
   \Rightarrow d_i>m/(q+2),
   $$

   以及

   $$
   q^3+q^2+q+1>(q+2)^2.
   $$

5. **primorial 屏障。**
   写出前 \(65\) 个素数列表，验证其素性和乘积；证明含至少 \(65\) 个不同素因子的整数不小于该乘积。

6. **因子矩引理。**
   定义有限支持的 \(e_\ell\)，交换有限求和；核心只有

   $$
   \left\lfloor\frac mD\right\rfloor\le\frac mD
   $$

   和不同素数幂的乘积公式。

7. **hinge–\(e_{C+1}\) 引理。**
   可形式化“两分数坐标压缩”：

   $$
   e_r(x,y,u')
   =
   xy e_{r-2}(u')+(x+y)e_{r-1}(u')+e_r(u').
   $$

   然后归纳把极小点压到至多一个分数坐标。

8. **容量传输归约。**
   不需要形式化 LP 对偶；直接形式化 hinge 的标量对偶

   $$
   (u-C)^+=\max_{t\in[0,1]}t(u-C)
   $$

   以及有限和换序即可。

精确复核脚本：
[round11_sparse_core_audit.py](sandbox:/mnt/data/round11_sparse_core_audit.py)

---

$$
\boxed{
\begin{aligned}
\textbf{final claim}
&\leftarrow
\begin{cases}
(RP_{64})\text{ 被反驳},\\
\text{纯 one-step 合取计数不可能给绝对 }C,\\
(SC_{64})\text{ 对 }m<P_{65}\text{ 成立},\\
L_{64}<6.239\cdot10^{-90}m,\\
\text{问题归约为真实 prime-power set system 的容量传输};
\end{cases}\\[2mm]
&\leftarrow
\textbf{lemmas }1\text{--}13;\\[2mm]
&\leftarrow
\textbf{unproved items: }
\begin{cases}
\text{U1：对 }m\ge P_{65}\text{ 证明绝对成本的 atomwise transport；}\\
\text{U2：独立重构并审定 P3 dense branch；}\\
\text{或 U3：构造满足真实乘法 floor 表的 T3 对手。}
\end{cases}
\end{aligned}}
$$
