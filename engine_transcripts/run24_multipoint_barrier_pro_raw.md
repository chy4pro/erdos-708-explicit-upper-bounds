# 合并结论

四条路线中，最强的严格结果是：

1. **T3 [PROVED]**：存在一个完全显式的无限族，且 \(m>10^{2958}\)，使得**任何**满足 (F)、非负、并且只支撑在高点因子上的证书，其值都不超过 \(L-1\)。这严格否定了“把所有高点的非负 shadow 证书装进同一个 LP”作为全尺度证明方案。构造中的实际窗口仍满足 \((\mathrm{SC}_{64})\)，所以它否定的是证明方法，不是原不等式。

2. **无条件改进 [PROVED]**：

$$
(\mathrm{SC}_{64})\qquad\text{对所有 }4096<m\le 10^{2942}
$$

成立。题面同一归约因此把

$$
g(n)\le 81n
$$

的范围安全地推进到所有 \(n\le 10^{980}\)。

3. **T2 [REFUTED as stated]**：对不等质量，统一系数 \(2/65\) 不可行；即使 65 个组都在 \((64/65,1]\) 内也会失败。最优统一系数是

$$
c_*=\frac{B-1}{\binom{65}{2}},
\qquad B=\sum_{i=1}^{65}b_i,
$$

由此只能统一保证总系数 \(B-1>63\)，不能保证 \(64\)。

4. **修正后的 T2 [PROVED]**：若某个高点确实存在 65 个两两素支撑的组，质量都在 \((64/65,1]\)，则可得到

$$
R>(B-1)\bigl(mQ^{-2/65}-1\bigr)
   >63\bigl(mk^{-2/65}-1\bigr).
$$

结合新的均值分岔，可把这类实例推进到

$$
m\le 10^{3013}.
$$

5. **T4 所要求的 \(o(\log\log m)\) [CONJECTURED]**：没有由 S2+单高点 S4 得到。事实上严格证明了一个方法屏障：该数值比较必然要求

$$
C(m)\gg \sqrt{\frac{\log m}{\log\log m}},
$$

所以 \(C(m)=(\log\log m)^{1/2}\) 不可能由这条单点路线推出。

---

## 1. 基础素数估计

### Lemma 1 [PROVED]：粗显式上界

对所有 \(y\ge16\)，

$$
\pi(y)\le \frac{8y}{\log y}.
$$

#### 证明

记

$$
\vartheta(y)=\sum_{p\le y}\log p.
$$

先对整数 \(n\) 证明

$$
\vartheta(n)\le 4n\log2.
$$

令 \(k=\lceil n/2\rceil\)。每个满足 \(k<p\le n\) 的素数都整除
\(\binom{2k}{k}\)，所以

$$
\vartheta(n)-\vartheta(k)
 \le \log\binom{2k}{k}
 \le 2k\log2.
$$

归纳假设给出

$$
\vartheta(n)\le 6k\log2\le4n\log2;
$$

最后一个不等式对偶数显然，对 \(n=2r+1\ge3\) 等价于
\(6(r+1)\le8r+4\)。

现在将素数分为 \(p\le\sqrt y\) 和 \(p>\sqrt y\)。后一部分中
\(\log p>\frac12\log y\)，故

$$
\pi(y)
 \le \sqrt y+\frac{2\vartheta(y)}{\log y}
 \le \sqrt y+\frac{8(\log2)y}{\log y}.
$$

当 \(y\ge16\) 时，\(\log y/\sqrt y\) 单调下降，并且

$$
\frac{\log16}{4}<\frac34<8(1-\log2),
$$

所以右端不超过 \(8y/\log y\)。证毕。

---

### Lemma 2 [PROVED]：粗显式下界

对整数 \(Q\ge16\)，

$$
\pi(2Q)\ge
\frac{2Q\log2-\log(2Q+1)}{\log(2Q)}.
$$

#### 证明

中心二项式系数满足

$$
\binom{2Q}{Q}\ge \frac{4^Q}{2Q+1}.
$$

另一方面，对每个 \(p\le2Q\)，Legendre 公式给出

$$
v_p\binom{2Q}{Q}
 =\sum_{a\ge1}
 \left(
 \Big\lfloor\frac{2Q}{p^a}\Big\rfloor
 -2\Big\lfloor\frac{Q}{p^a}\Big\rfloor
 \right)
 \le\lfloor\log_p(2Q)\rfloor.
$$

因此每个素数对二项式系数的贡献不超过 \(2Q\)，从而

$$
\binom{2Q}{Q}\le(2Q)^{\pi(2Q)}.
$$

取对数即得结论。∎

---

## 2. 对 A2“直接求和或去重”的最小对抗例

### Lemma 3 [REFUTED candidate]

即使只有两个高点，局部 all-pairs 证书的“求和”与“去重后保持原系数”都可能不满足 (F)。

取

$$
1000<p_1<\cdots<p_{66}
$$

为连续的 66 个素数，令所有 \(\alpha_{p_i,1}=1\)。设

$$
P=\prod_{i=1}^{66}p_i,\qquad
k_1=P/p_{65},\qquad k_2=P/p_{66},
$$

并取

$$
m=64\max(k_1,k_2),\qquad
I=\{P,P+1,\ldots,P+m-1\}.
$$

由于 \(p_{65},p_{66}>64\)，有 \(P>m\)，所以这是合法的
\(x=P-1\) 窗口。并且

$$
H=\sum_{i=1}^{66}\frac1{p_i}<\frac{66}{1000}<\frac{17}{16}.
$$

两个高点分别对应两个重合 64 个顶点的 \(K_{65}\)。把 pair shadow 去重后，所得边集是 \(K_{66}\) 去掉一条边，共

$$
\binom{66}{2}-1=2144
$$

条边。若每条仍取系数 \(2/65\)，则在 \(n=P\) 处证书值为

$$
\frac{2}{65}\cdot2144
 =\frac{4288}{65}
 =65+\frac{63}{65}.
$$

但

$$
(S_0(P)-1)^+=66-1=65.
$$

因此 (F) 失败。

这同时是抽象多重集反例和同余窗口反例。

---

# 3. T3：所有非负高点因子证书的显式障碍

## 3.1 构造

对任意满足

$$
M\in10\mathbb Z,\qquad M\ge2000
$$

的整数，定义

$$
Q=2^M,\qquad
m=(2Q)^{65}=2^{65(M+1)}.
$$

令

$$
\mathcal P_M
 =\{p\text{ prime}:Q^{9/10}<p\le2Q\},
\qquad N=|\mathcal P_M|.
$$

取原子

$$
\alpha_{p,1}=1\quad(p\in\mathcal P_M),
\qquad
\alpha_{p,j}=0\quad\text{其余情形}.
$$

于是

$$
S_0(n)=|\{p\in\mathcal P_M:p\mid n\}|.
$$

再令

$$
P_M=\prod_{p\in\mathcal P_M}p,
\qquad
x=P_M-1,\qquad
I_M=\{P_M,\ldots,P_M+m-1\}.
$$

这是完全确定的无限序列。最小参数 \(M=2000\) 时，

$$
\log_{10}m
 =65\cdot2001\log_{10}2
 >39153>2958.
$$

---

## 3.2 参数核验

### Lemma 4 [PROVED]

对所有上述 \(M\)，有

$$
N\ge\frac{Q}{2\log(2Q)},
\qquad
H<\frac9{10}<\frac{17}{16},
\qquad
p\le \frac m{64}\quad(p\in\mathcal P_M).
$$

#### 证明：\(N\) 的下界

由 Lemma 2，且 \(Q\) 极大，

$$
\pi(2Q)\ge\frac{Q}{\log(2Q)}.
$$

具体地，因为 \(\log2>2/3\)，

$$
2Q\log2-\log(2Q+1)
 >\frac43Q-\log(2Q+1)>Q.
$$

另外

$$
\pi(Q^{9/10})\le Q^{9/10}.
$$

而

$$
Q^{9/10}\le\frac{Q}{2\log(2Q)}
$$

等价于

$$
2^{M/10}\ge2(M+1)\log2,
$$

它在 \(M=2000\) 时成立，并且左端与右端之比此后严格增加。因此

$$
N
 \ge \pi(2Q)-\pi(Q^{9/10})
 \ge\frac{Q}{2\log(2Q)}.
$$

#### 证明：均值上界

分部求和给出

$$
\sum_{Q^{9/10}<p\le2Q}\frac1p
 \le \frac{\pi(2Q)}{2Q}
   +\int_{Q^{9/10}}^{2Q}\frac{\pi(t)}{t^2}\,dt.
$$

由 Lemma 1，

$$
H
 \le\frac8{\log(2Q)}
 +8\log\frac{\log(2Q)}{\log(Q^{9/10})}.
$$

代入 \(Q=2^M\)，

$$
H
 \le
 \frac8{(M+1)\log2}
 +8\log\frac{M+1}{(9/10)M}.
$$

当 \(M\ge2000\) 时，

$$
\frac8{(M+1)\log2}<\frac1{150},
$$

并且

$$
\frac{M+1}{(9/10)M}
 =1+\frac{M+10}{9M}
 \le1+\frac{67}{600}.
$$

利用 \(\log(1+u)\le u\)，

$$
H<\frac1{150}+8\cdot\frac{67}{600}
 =\frac1{150}+\frac{67}{75}
 =\frac9{10}.
$$

最后

$$
\frac m{64}=2^{59}Q^{65}>2Q,
$$

故支撑限制成立。∎

---

## 3.3 \(L\) 的下界

### Lemma 5 [PROVED]

对上述系统，

$$
L\ge\binom N{65}
 \ge\frac{(N/2)^{65}}{65!}.
$$

#### 证明

对每个 \(65\)-元子集 \(A\subset\mathcal P_M\)，令

$$
k_A=\prod_{p\in A}p.
$$

由于 \(p\le2Q\)，

$$
k_A\le(2Q)^{65}=m.
$$

唯一分解保证不同 \(A\) 给出不同的 \(k_A\)，并且

$$
S_0(k_A)=65.
$$

每个这样的点对 \(L\) 恰好贡献 \(1\)，所以

$$
L\ge\binom N{65}.
$$

由于 \(N\gg128\)，所有因子 \(N-i\), \(0\le i\le64\)，都至少为 \(N/2\)，故

$$
\binom N{65}
 =\frac{\prod_{i=0}^{64}(N-i)}{65!}
 \ge\frac{(N/2)^{65}}{65!}.
$$

∎

---

## 3.4 对任意非负证书的统一上界

令

$$
\mathcal H=\{k\le m:S_0(k)>64\},
$$

并设 \(c_D\ge0\) 满足：

1. \(c_D=0\)，除非 \(D\mid k\) 对某个 \(k\in\mathcal H\)；
2. 对所有 \(n\ge1\)，

   $$
   \sum_{D\mid n}c_D\le(S_0(n)-1)^+.
   \tag{F}
   $$

定义证书值

$$
V(c)=\sum_Dc_D\Big\lfloor\frac mD\Big\rfloor.
$$

### Lemma 6 [PROVED]

每个这样的证书满足

$$
V(c)<N\,2^{65}Q^{316/5}.
$$

#### 证明

首先，若 \(D\) 含有至多一个 \(\mathcal P_M\) 中的素数，则

$$
S_0(D)\le1.
$$

在 (F) 中取 \(n=D\)，得到

$$
\sum_{E\mid D}c_E\le0.
$$

所有系数非负，故特别有 \(c_D=0\)。

因此每个非零系数对应的 \(D\) 至少含有两个选定素数，于是

$$
D>Q^{9/10}Q^{9/10}=Q^{9/5}.
\tag{3.1}
$$

另一方面，所有支撑模数都是某个 \(k\le m\) 的因子，故都整除

$$
\Lambda=\operatorname{lcm}(1,2,\ldots,m).
$$

所有选定素数也整除 \(\Lambda\)，所以

$$
S_0(\Lambda)=N.
$$

在 (F) 中取 \(n=\Lambda\)，得到

$$
\sum_Dc_D\le N-1.
\tag{3.2}
$$

结合 (3.1)、(3.2)，

$$
\begin{aligned}
V(c)
&=\sum_Dc_D\Big\lfloor\frac mD\Big\rfloor\\
&<\frac{m}{Q^{9/5}}\sum_Dc_D\\
&\le (N-1)\frac{(2Q)^{65}}{Q^{9/5}}\\
&<N\,2^{65}Q^{316/5}.
\end{aligned}
$$

∎

这也给出了显式 LP 对偶证书：

* 对“含至多一个选定素数”的模数，使用 \(n=D\) 的零容量约束；
* 对其余模数，使用 \(n=\Lambda\) 的约束并乘以 \(m/Q^{9/5}\)。

---

## 3.5 常数比较

### Lemma 7 [PROVED]

对所有 \(M\ge2000\)，

$$
V(c)<2^{-247}L.
$$

特别地，

$$
V(c)\le L-1.
$$

#### 证明

若 \(V(c)=0\) 则显然。否则由 Lemmas 4–6，

$$
\frac{L}{V(c)}
>
\frac{N^{64}}
 {2^{130}65!\,Q^{316/5}}
\ge
\frac{Q^{4/5}}
 {2^{194}65!\,[\log(2Q)]^{64}}.
\tag{3.3}
$$

取 \(Q=2^M\)。函数

$$
M\longmapsto
\frac{2^{4M/5}}{(M+1)^{64}}
$$

在 \(M\ge2000\) 上递增，因为其对数导数满足

$$
\frac45\log2-\frac{64}{M+1}
>
\frac{8}{15}-\frac1{30}
=\frac12.
$$

因此只需考察 \(M=2000\)。此时

$$
Q^{4/5}=2^{1600},
$$

$$
\log(2Q)<M+1=2001<2^{11},
$$

并且粗略地

$$
65!<65^{65}<2^{7\cdot65}=2^{455}.
$$

故 (3.3) 给出

$$
\frac{L}{V(c)}
>
2^{1600-194-455-11\cdot64}
=2^{247}.
$$

由于 \(L\ge2\)，

$$
V(c)<\frac L2\le L-1.
$$

∎

---

## Theorem A [PROVED — T3]

对每个 \(M\in10\mathbb Z\), \(M\ge2000\)，上述原子系统、长度

$$
m_M=2^{65(M+1)}
$$

及窗口

$$
I_M=\{P_M,\ldots,P_M+m_M-1\}
$$

满足全部稀疏核假设，并且：

> 对任何非负、满足 (F)、且支撑在高点因子上的证书，
>
> $$
> \sum_Dc_D\Big\lfloor\frac{m_M}{D}\Big\rfloor\le L-1.
> $$

所以 T3 的第一种结论成立，而且比“某种 band rule 失败”更强：**整个非负高点因子 LP 都不足以证明这些实例的 \((\mathrm{SC}_{64})\)。**

---

## 3.6 同余窗口核验：它不是 SC 反例

### Lemma 8 [PROVED]

上述窗口实际满足

$$
R\ge L.
$$

#### 证明

因为 \(P_M\) 被每个选定素数整除，对 \(1\le t\le m-1\)，

$$
S_0(P_M+t)=S_0(t).
$$

并且

$$
S_0(P_M)=N.
$$

所以

$$
R
=(N-1)+
 \sum_{t=1}^{m-1}(S_0(t)-1)^+.
$$

另一方面

$$
L
=\sum_{t=1}^{m-1}(S_0(t)-64)^+
 +(S_0(m)-64)^+.
$$

逐项有

$$
(S_0(t)-1)^+\ge(S_0(t)-64)^+,
$$

而且

$$
(S_0(m)-64)^+\le N-64\le N-1.
$$

因此 \(R\ge L\)。∎

这说明障碍完全位于“非负 divisor-shadow 证书”与真实 hinge 之间；真实 \(R\) 中必须利用不能由这种证书表达的重叠信息。

---

# 4. T2：不等质量 pair certificate

## 4.1 原系数 \(2/65\) 不成立

### Lemma 9 [REFUTED]

设 65 个两两素支撑的组质量均为

$$
b_i=\frac{64}{65}+\varepsilon,
\qquad 0<\varepsilon<\frac1{65}.
$$

总质量为

$$
B=64+65\varepsilon.
$$

若所有 pair products 都取系数 \(2/65\)，则当全部 65 个组同时整除 \(n\) 时，证书值为

$$
\frac2{65}\binom{65}{2}=64.
$$

但此时右端容量只有

$$
(S_0(n)-1)^+=B-1=63+65\varepsilon<64.
$$

所以 (F) 失败。

这可以直接算术实现：取 65 个大于 \(1000\) 的素数，

$$
\alpha_{p_i,1}=\frac{64}{65}+\frac1{10000},
\qquad
k=\prod_{i=1}^{65}p_i,
\qquad m=64k.
$$

则 \(H<17/16\)、支撑条件成立，而 claimed coefficient 在 \(n=k\) 处失败。

此外，“总质量 \(>64\) 自动能分成 65 个质量在
\((64/65,1]\) 的组”也不成立。抽象反例是 107 个质量 \(3/5\) 的项目：

$$
107\cdot\frac35=\frac{321}{5}>64.
$$

一个组含一个项目时质量 \(3/5<64/65\)，含两个时质量 \(6/5>1\)，所以不存在一个合格组，更不可能存在 65 个。

---

## 4.2 最优修正系数

### Lemma 10 [PROVED]

设有 65 个两两素支撑的组 \(G_i\)，对应模数 \(D_i\)，质量

$$
\frac{64}{65}<b_i\le1,
\qquad
B=\sum_{i=1}^{65}b_i>64.
$$

令

$$
c_*=\frac{B-1}{\binom{65}{2}}
    =\frac{B-1}{2080}.
$$

则

$$
c_*\sum_{1\le i<j\le65}
  1[D_iD_j\mid n]
\le (S_0(n)-1)^+
$$

对所有 \(n\) 成立。

此外，\(c_*\) 是所有 pair 使用同一系数时的最优值。

#### 证明

写

$$
b_i=1-d_i,\qquad
0\le d_i<\frac1{65},
\qquad
\Delta=\sum_i d_i=65-B<1.
$$

若恰有 \(t\) 个 \(D_i\) 整除 \(n\)，证书值为

$$
c_*\binom t2
 =\frac{(64-\Delta)t(t-1)}{4160}.
$$

这些组对 \(S_0(n)\) 的贡献至少是

$$
t-\Delta_T,
\qquad
\Delta_T=\sum_{i\in T}d_i
 \le\min\left(\Delta,\frac t{65}\right).
$$

所以只需证明

$$
\frac{(64-\Delta)t(t-1)}{4160}
\le t-1-\min\left(\Delta,\frac t{65}\right).
\tag{4.1}
$$

对固定 \(t\)，两边之差作为 \(\Delta\) 的函数：

* 在 \(\Delta\le t/65\) 时单调下降；
* 在 \(\Delta\ge t/65\) 时单调上升。

故最坏点是 \(\Delta=t/65\)。代入后，差为

$$
\frac{(t-65)(t^2-4096t+4160)}{270400}.
$$

对 \(2\le t\le65\)，第一因子非正；第二因子在该区间严格为负。因此差非负。

当 \(t=0,1\) 时证书值为零，结论也成立。

最优性来自全部 65 个组同时整除的约束：

$$
c\binom{65}{2}\le B-1.
$$

故 \(c\le c_*\)。∎

特别地，\(c_*=2/65\) 当且仅当 \(B=65\)，也就是所有 \(b_i=1\)。

---

## 4.3 算术价值

### Lemma 11 [PROVED]

在 Lemma 10 的条件下，设

$$
Q=\prod_{i=1}^{65}D_i\mid k\le m.
$$

则

$$
R\ge
(B-1)\left(mQ^{-2/65}-1\right)
>
63\left(mk^{-2/65}-1\right).
\tag{4.2}
$$

#### 证明

由 S1 和 Lemma 10，

$$
R\ge
c_*\sum_{i<j}\Big\lfloor\frac{m}{D_iD_j}\Big\rfloor.
$$

而

$$
\prod_{i<j}D_iD_j=Q^{64}.
$$

AM–GM 给出

$$
\sum_{i<j}\frac1{D_iD_j}
 \ge2080Q^{-2/65}.
$$

再使用 \(\lfloor u\rfloor\ge u-1\)，

$$
\begin{aligned}
R
&\ge c_*
 \left(
 2080mQ^{-2/65}-2080
 \right)\\
&=(B-1)(mQ^{-2/65}-1).
\end{aligned}
$$

由于 \(B-1>63\) 且 \(Q\le k\)，得到 (4.2)。∎

---

# 5. 一个新的无条件均值分岔

### Lemma 12 [PROVED]

令

$$
A=\sum_{p,j}\alpha_{p,j}.
$$

则

$$
A\le\pi(m/64)
$$

并且

$$
R\ge m(H-1)-A.
\tag{5.1}
$$

#### 证明

每个素数上的总质量不超过 1，故

$$
A\le\#\{p:p\le m/64\}=\pi(m/64).
$$

同时

$$
\sum_{k\le m}S_0(k)
 =\sum_{p,j}\alpha_{p,j}
   \Big\lfloor\frac{m}{p^j}\Big\rfloor
 \ge mH-A.
$$

长度 \(m\) 的任意区间中，\(p^j\) 的倍数至少有
\(\lfloor m/p^j\rfloor\) 个，因此

$$
\sum_{b\in I}S_0(b)\ge\sum_{k\le m}S_0(k).
$$

最后

$$
(S_0(b)-1)^+\ge S_0(b)-1,
$$

所以

$$
R\ge\sum_{b\in I}S_0(b)-m
 \ge mH-A-m.
$$

∎

这是严格的一阶补偿：当 \(H\) 明显大于 \(1\) 时，不需要 shadow theorem。

---

# 6. 无条件推进到 \(10^{2942}\)

定义

$$
C_{17}:=\frac{(17/16)^{65}}{65!}
 =6.2380774565\ldots\times10^{-90},
$$

$$
\rho_0:=
\frac1{8(2887\log10-\log64)}
 =1.8815654553\ldots\times10^{-5},
$$

$$
h_0:=1+\rho_0+C_{17},
$$

$$
C_0:=\frac{h_0^{65}}{65!}
 =1.2139502553\ldots\times10^{-91},
$$

以及

$$
A_4:=\frac{32}{3}(1-6^{-31})
 =10.6666666666\ldots.
$$

### Lemma 13 [PROVED]

对所有

$$
10^{2887}<m\le10^{2942},
$$

有 \(L\le R\)。

#### 证明

由 Lemma 1，

$$
\frac{A}{m}
\le\frac{\pi(m/64)}m
\le\frac1{8\log(m/64)}
<\rho_0.
$$

分两种情况。

### Case 1：\(H\ge h_0\)

由 Lemma 12，

$$
R\ge m(H-1)-A
   \ge m(H-1-\rho_0)
   \ge mC_{17}.
$$

而 S2 给出

$$
L
\le\frac{mH^{65}}{65!}
<mC_{17},
$$

因为 \(H<17/16\)。故 \(L<R\)。

### Case 2：\(H<h_0\)

此时 S2 给出

$$
L<mC_0.
$$

若 \(L=0\)，结论显然。否则存在一个高点 \(k\le m\)，S4 给出

$$
R\ge A_4\frac{m}{k^{1/32}}
 \ge A_4m^{31/32}.
$$

下面核对常数。容易验证

$$
C_0<1.22\times10^{-91},
\qquad
A_4>10.666.
$$

又因为

$$
m^{1/32}\le10^{2942/32}
 =10^{91}10^{15/16},
$$

且精确整数比较

$$
433^{16}>
10^{15}50^{16}
$$

说明

$$
10^{15/16}<\frac{433}{50}=8.66.
$$

因此

$$
C_0m^{1/32}
<
1.22\cdot8.66
=10.5652
<10.666
<A_4.
$$

故

$$
L<C_0m<A_4m^{31/32}\le R.
$$

∎

题面已经给出 \(m\le10^{2887.45}\) 的范围，所以拼接得到：

## Theorem B [PROVED]

$$
\boxed{
(\mathrm{SC}_{64})\text{ 对所有 }4096<m\le10^{2942}\text{ 成立。}
}
$$

同一 published reduction 给出安全后果：

$$
\boxed{
g(n)\le81n\qquad(n\le10^{980}).
}
$$

因为

$$
8(10^{980})^3=8\cdot10^{2940}<10^{2942}.
$$

更精确地，上述新分岔与单点 S4 的临界值为

$$
M_{\mathrm{crit}}
 :=
\left(\frac{A_4}{C_0}\right)^{32},
$$

并且

$$
\log_{10}M_{\mathrm{crit}}
 =2942.202490649766\ldots.
$$

---

# 7. 修正后的 T2 推进到 \(10^{3013}\)

### Theorem C [PROVED, conditional only on the stated 65-group decomposition]

假设 \(L>0\)，且存在一个高点 \(k\le m\)，其活跃素数可以分为 65 个两两不交的组，满足

$$
\frac{64}{65}<b_i\le1.
$$

则对所有

$$
m\le10^{3013}
$$

均有 \(L\le R\)。

#### 证明

当 \(m\le10^{2942}\) 时由 Theorem B。

现在设

$$
10^{2942}<m\le10^{3013}.
$$

仍使用 Lemma 12 的均值分岔。高均值情形直接成立；低均值情形有

$$
L<C_0m.
$$

Lemma 11 给出

$$
R>63(m^{63/65}-1).
$$

而

$$
C_0m^{2/65}
<
1.22\times10^{-91}\,
10^{6026/65}
<62.3,
$$

同时 \(m>10^{2942}\) 给出

$$
63(1-m^{-63/65})>62.9.
$$

故

$$
C_0m<63(m^{63/65}-1)<R.
$$

∎

对应的忽略极小 floor 修正后的临界指数是

$$
\frac{65}{2}\log_{10}\frac{63}{C_0}
 =3013.2420389\ldots.
$$

所以 T2 的正确版本不仅把原先的 \(2957\) 目标保住，还在均值分岔后推进到了安全整数指数 \(3013\)。未解决之处是：一般高点并不必然具有这种 65-group 分解。

---

# 8. T4：一般增长阈值与方法屏障

## 8.1 一般单点准则

### Lemma 14 [PROVED]

令 \(N\ge2\)，阈值为 \(r=2N\)。若

$$
m^{1/N}
\le
\frac N3(1-6^{1-N})
\frac{(2N+1)!}{(17/16)^{2N+1}},
\tag{8.1}
$$

则

$$
\sum_{k\le m}(S_0(k)-2N)^+
\le R.
$$

#### 证明

若某个 \(k\) 满足 \(S_0(k)>2N\)，将活跃质量打包为 \(N\) 个组，每组质量在 \((4/3,2]\)。

一个显式打包算法是：

1. 将所有质量 \(>2/3\) 的项目两两配对；
2. 剩余项目按任意顺序贪心累加，首次超过 \(4/3\) 时结束一组。

每组质量不超过 2。若得到少于 \(N\) 组，则已完成组的总质量至多 \(2(N-1)\)，剩余质量至多 \(4/3\)，总质量小于

$$
2N-\frac23,
$$

与总质量 \(>2N\) 矛盾。

对应模数 \(D_1,\ldots,D_N\) 两两互素，且 \(D_i\ge6\)。系数 \(1/3\) 可行，并且

$$
R\ge
\frac N3(1-6^{1-N})m\,k^{-1/N}
\ge
\frac N3(1-6^{1-N})m^{1-1/N}.
\tag{8.2}
$$

另一方面，对 \(a_p\in[0,1]\)，

$$
\left(\sum_pa_p-2N\right)^+
 \le e_{2N+1}(a_p).
$$

一种直接证明是取独立 Bernoulli 随机变量 \(X_p\)、
\(\mathbb E X_p=a_p\)，注意对整数 \(X=\sum X_p\)，

$$
\binom X{2N+1}\ge X-2N.
$$

取期望即得。

因此

$$
L_{2N}
\le
\frac{m(17/16)^{2N+1}}{(2N+1)!}.
$$

条件 (8.1) 正好保证该上界不超过 (8.2)。∎

---

## 8.2 一个完全显式的全尺度阈值

### Corollary 15 [PROVED for the sparse core]

令 \(X=\log m\)。定义

$$
r(m)=
\begin{cases}
64,&m<\exp(e^8),\\[2mm]
2\left\lceil
3\sqrt{\dfrac{X}{\log X}}
\right\rceil,
&m\ge\exp(e^8).
\end{cases}
$$

则对所有 \(m>4096\)，

$$
\sum_{k\le m}(S_0(k)-r(m))^+\le R.
$$

特别地，对大 \(m\)，

$$
r(m)\le
6\sqrt{\frac{\log m}{\log\log m}}+2.
$$

#### 核验

令

$$
N=\left\lceil3\sqrt{\frac X{\log X}}\right\rceil,
\qquad Y=\log X\ge8.
$$

使用

$$
(2N+1)!\ge N^{N+1},
\qquad
\frac{17}{16}<e^{1/16},
\qquad
\frac N3(1-6^{1-N})\ge\frac N4,
$$

可将 (8.1) 归约为

$$
\frac XN+\frac{2N+1}{16}+\log4
\le(N+2)\log N.
\tag{8.3}
$$

由

$$
N\ge3\sqrt{X/Y},\qquad
\log N\ge Y/3
$$

得到右端至少为 \(\sqrt{XY}\)。左端至多为

$$
\frac13\sqrt{XY}
+\frac38\sqrt{X/Y}
+\frac{35}{16},
$$

在 \(Y\ge8\) 时严格小于 \(\sqrt{XY}\)。故 (8.3) 成立。

这只是复现 \(O(\sqrt{\log m/\log\log m})\) 的单点尺度，不优于已有的 \(O(\log\log m)\) 结果。

---

## 8.3 单点 S4 + S2 的必要屏障

### Lemma 16 [PROVED]

如果使用 Lemma 14 的数值比较来证明阈值 \(2N\)，则必然有

$$
\log m
\le
3N^2\log(3N).
\tag{8.4}
$$

#### 证明

若 (8.1) 成立，则由于

$$
\frac N3(1-6^{1-N})<N,
\qquad
(2N+1)!\le(2N+1)^{2N+1},
\qquad
(17/16)^{2N+1}>1,
$$

有

$$
m^{1/N}
<
N(2N+1)^{2N+1}.
$$

取对数，

$$
\frac{\log m}{N}
<
\log N+(2N+1)\log(2N+1)
\le(2N+2)\log(3N).
$$

当 \(N\ge2\) 时 \(2N+2\le3N\)，得到 (8.4)。∎

于是这条路线必然要求

$$
N\gtrsim
\sqrt{\frac{\log m}{\log\log m}}.
$$

特别地，

$$
N=(\log\log m)^{1-\delta}
$$

或

$$
N=(\log\log m)^{1/2}
$$

最终都违反 (8.4)。

这不是对 \((\mathrm{TH}_C)\) 本身的反驳，而是对“T4 可由 S2 与一个单高点 S4 数值比较得到”的严格反驳。

---

# 9. 可复核运算

下面只使用 Python 标准库，重新核验全部关键常数、T2 的 65 个子集极值以及 T3 的 \(2^{247}\) 裕量。

```python
from decimal import Decimal, getcontext
from fractions import Fraction
from math import factorial

getcontext().prec = 80
D = Decimal

ln2 = D(2).ln()
ln10 = D(10).ln()

# Universal SC_64 extension
C17 = (D(17) / D(16)) ** 65 / D(factorial(65))
rho0 = D(1) / (D(8) * (D(2887) * ln10 - D(64).ln()))
h0 = D(1) + rho0 + C17
C0 = h0 ** 65 / D(factorial(65))
A4 = D(32) / D(3) * (D(1) - D(6) ** (-31))

log10_Mcrit = D(32) * (A4 / C0).ln() / ln10

assert rho0 < D("1.9e-5")
assert C0 < D("1.22e-91")
assert A4 > D("10.666")
assert log10_Mcrit > D(2942)

# 10^(15/16) < 8.66, by exact integer arithmetic
assert 433 ** 16 > 10 ** 15 * 50 ** 16

# Corrected unequal-mass pair certificate.
# The worst deficit is Delta=t/65; this is the exact resulting slack.
for t in range(2, 66):
    slack = Fraction(
        (t - 65) * (t * t - 4096 * t + 4160),
        270400,
    )
    assert slack >= 0

# Original-moment conditional pair range and improved range
assert (
    D("6.24e-90") * D(10) ** (D(2 * 2957) / D(65))
    < D("60.3")
)
assert (
    C0 * D(10) ** (D(2 * 3013) / D(65))
    < D("62.3")
)

# T3, M=2000
M = D(2000)

H_upper = (
    D(8) / ((M + 1) * ln2)
    + D(8) * ((M + 1) / (D("0.9") * M)).ln()
)
assert H_upper < D("0.9")

# Q^(4/5) versus 2^194 * 65! * log(2Q)^64:
# 65! < 2^(7*65), log(2Q) < 2^11 at M=2000.
exponent_margin = (
    Fraction(4, 5) * 2000
    - 194
    - 7 * 65
    - 11 * 64
)
assert exponent_margin == 247

# The first m in the T3 sequence is already beyond 10^2958.
assert D(65) * D(2001) * D(2).log10() > D(2958)

print("C17 =", C17)
print("rho0 =", rho0)
print("C0 =", C0)
print("A4 =", A4)
print("log10 Mcrit =", log10_Mcrit)
print("T3 H upper =", H_upper)
```

预期核心输出为

```text
C17 = 6.2380774565412187...E-90
rho0 = 0.00001881565455363999...
C0 = 1.2139502553347811...E-91
A4 = 10.666666666666666...
log10 Mcrit = 2942.202490649766...
T3 H upper = 0.8526510218112669...
```

---

# 10. Lean 形式化所需内容

形式化可以分为四个彼此独立的文件。

### `PrimeBounds.lean`

需要：

1. \(\vartheta(n)\le4n\log2\) 的强归纳；
2. \(k<p\le n\Rightarrow p\mid\binom{2k}{k}\)；
3. \(\pi(y)\le8y/\log y\)；
4. 中心二项式下界；
5. \(v_p\binom{2Q}{Q}\le\lfloor\log_p(2Q)\rfloor\)；
6. Lemma 2 的 \(\pi(2Q)\) 下界；
7. 有限 Stieltjes/Abel 分部求和版本，或直接使用素数列表上的离散 summation by parts。

### `CertificateObstruction.lean`

定义：

$$
\mathcal P_M=\{p:\operatorname{Prime}(p)\land Q^{9/10}<p\le2Q\}.
$$

需要：

1. `Finset.card` 形式的 \(N\) 下界；
2. 65 元子集到乘积的单射；
3. \(\binom N{65}\) 个高点；
4. 若模数只含至多一个选定素数，则其系数为零；
5. `lcmRange m` 使所有支撑模数同时整除；
6. 总系数 \(\le N-1\)；
7. 最终的 \(2^{247}\) 比较。

这里完全不需要在 Lean 中枚举 \(2^{2000}\) 附近的素数；只需形式化二项式系数给出的基数下界。

### `UnequalPairs.lean`

需要：

1. deficits \(d_i\)；
2. \(\Delta_T\le\min(\Delta,t/65)\)；
3. 分段线性函数的极小点位于 \(\Delta=t/65\)；
4. 多项式

   $$
   (t-65)(t^2-4096t+4160)\ge0
   $$

   在 \(2\le t\le65\) 上的有限整数核验；
5. pair-product AM–GM；
6. floor 误差。

### `MeanSplit.lean`

需要：

1. \(\sum\alpha_{p,j}\le\pi(m/64)\)；
2. 区间倍数计数不小于 \(\lfloor m/q\rfloor\)；
3. Lemma 12；
4. S2、S4 作为已经形式化的输入定理；
5. 数值结论

   $$
   C_0<1.22\cdot10^{-91},\quad
   A_4>10.666,\quad
   10^{15/16}<433/50.
   $$

最后一个可直接交给 `norm_num`，前两个宜使用有理上下界和 `Real.log` 的区间证明。

---

# 11. 最终状态

### T1

**原命题 \((\mathrm{SC}_{64})\) 对所有 \(m\)：CONJECTURED。**

但其中提出的以下证明框架已被严格否定：

> 将所有高点产生的、支撑在高点因子上的非负 shadow 证书放进一个全局 LP，并期望其最优值总能达到 \(L\)。

该框架由 Theorem A **REFUTED**。

### T2

**REFUTED as stated。**

统一系数 \(2/65\) 只在全部 65 个组质量恰为 1 时可行。修正后的最优统一系数及 \(>63\) 的算术价值已经 **PROVED**。

### T3

**PROVED。**

显式无限族：

$$
M\in10\mathbb Z,\ M\ge2000,\quad
Q=2^M,\quad
m=(2Q)^{65},
$$

以及

$$
\mathcal P_M=\{Q^{9/10}<p\le2Q\}
$$

满足目标，且裕量至少为 \(2^{247}\)。

### T4

所要求的

$$
C(m)=o(\log\log m)
$$

仍为 **CONJECTURED**。S2 与一个 S4 单点 shadow 的组合被 Lemma 16 阻断。一个显式但较弱的

$$
C(m)\le
6\sqrt{\frac{\log m}{\log\log m}}+2
$$

稀疏核版本已经 **PROVED**。

---

# final claim ← lemmas ← unproved items

$$
\boxed{
\text{T3}
\leftarrow
\text{Lemmas 1--8}
\leftarrow
\varnothing
}
$$

$$
\boxed{
(\mathrm{SC}_{64})\text{ for }m\le10^{2942}
\leftarrow
\text{Lemmas 1, 12, 13 + S2 + S4}
\leftarrow
\varnothing
}
$$

$$
\boxed{
\text{corrected pair bound through }10^{3013}
\leftarrow
\text{Lemmas 10--13}
\leftarrow
\text{存在一个合格的 65-group 高点}
}
$$

$$
\boxed{
(\mathrm{SC}_{64})\text{ for all }m
\leftarrow
\text{需要 signed / non-divisor / residue-sensitive 聚合}
\leftarrow
\text{当前未证明}
}
$$

$$
\boxed{
\mathrm{TH}_{o(\log\log m)}
\leftarrow
\text{需要真正的多高点算术增益}
\leftarrow
\text{不能由 S2 + 单点 S4 数值比较得到}
}
$$
