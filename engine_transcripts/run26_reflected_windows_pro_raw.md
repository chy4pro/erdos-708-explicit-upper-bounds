# 结论

**[PROVED — T3]** 窗口自适应的非负除数证书 LP 仍不足以证明 \((SC_{64})\)。存在一个完全显式的无限族，满足全部原始假设，并且对相应窗口

$$
W(x)<L,
$$

甚至

$$
\frac{W(x)}{L}\longrightarrow 0.
$$

这个无限族只有 **一个** \(S_0>72\) 的窗口热点，因此“冷区 pair certificate + 少量热点修补”的方案在一般情形下也不能成立。

同时，这个族本身满足

$$
R\ge L+63.
$$

所以它**没有反驳 \((SC_{64})\) 本身**；它精确反驳的是：

1. T1 中“每个窗口都存在价值至少 \(L\) 的 \((F_I)\)-证书”；
2. T2 的“每个对偶 cover 的费用至少 \(L\)”；
3. 更一般地，任何固定阈值 \(C\ge2\) 下仅使用该 \(W\)-LP 的证明路线。

下面给出完整推导。

---

## 1. 记号

对任意整数阈值 \(C\ge2\)，写

$$
h_C(t):=(t-C)^+,\qquad
L_C:=\sum_{k=1}^m h_C(S_0(k)).
$$

窗口侧仍使用阈值 \(1\)：

$$
h_1(t)=(t-1)^+.
$$

对应的证书 LP 为

$$
W(I):=
\max\left\{
\sum_{D\le m}c_D\Big\lfloor\frac mD\Big\rfloor:
c_D\ge0,\ 
\sum_{\substack{D\le m\\D\mid b}}c_D\le h_1(S_0(b))
\ \forall b\in I
\right\}.
$$

\(D>m\) 的目标系数为零，故可完全删去。

---

## 2. A1 中的窗口矩估计

### 引理 1 [PROVED]：窗口一阶矩和热点个数

在原始假设

$$
p^j\le \frac m{64},\qquad
H=\sum_{p,j}\frac{\alpha_{p,j}}{p^j}<\frac{17}{16}
$$

下，对任意长度 \(m\) 的窗口 \(I\)，

$$
\sum_{b\in I}S_0(b)
<
\frac{1105}{1024}m.
$$

特别地，令

$$
T_{72}:=\{b\in I:S_0(b)>72\},
$$

则

$$
|T_{72}|
<
\frac{1105}{73728}m
<0.014988\,m.
$$

#### 证明

长度 \(m\) 的窗口中 \(d\) 的倍数个数满足

$$
N_I(d)\le \frac md+1.
$$

由于 \(d\le m/64\)，有 \(1\le m/(64d)\)，故

$$
N_I(d)\le \frac{65}{64}\frac md.
$$

于是

$$
\begin{aligned}
\sum_{b\in I}S_0(b)
&=\sum_{p,j}\alpha_{p,j}N_I(p^j)\\
&\le \frac{65}{64}m
  \sum_{p,j}\frac{\alpha_{p,j}}{p^j}\\
&<\frac{65}{64}\frac{17}{16}m
 =\frac{1105}{1024}m.
\end{aligned}
$$

而

$$
72|T_{72}|<\sum_{b\in T_{72}}S_0(b)
\le\sum_{b\in I}S_0(b).
$$

证毕。

---

### 引理 2 [PROVED]：截断后的窗口高阶矩

令

$$
a_p(b):=\sum_j\alpha_{p,j}\mathbf 1_{p^j\mid b},
\qquad
h_p:=\sum_j\frac{\alpha_{p,j}}{p^j}.
$$

对 \(\ell\ge1\)，定义只保留乘积模数 \(D\le m\) 的部分

$$
E_{\ell,\le m}(b):=
\sum_{\substack{p_1<\cdots<p_\ell\\
j_1,\ldots,j_\ell\ge1\\
D=\prod_i p_i^{j_i}\le m\\
D\mid b}}
\prod_{i=1}^{\ell}\alpha_{p_i,j_i}.
$$

则

$$
\sum_{b\in I}E_{\ell,\le m}(b)
\le
2m\,e_\ell((h_p)_p)
\le
\frac{2mH^\ell}{\ell!}.
$$

而在 \(K=\{1,\ldots,m\}\) 上，

$$
E_{\ell,\le m}(k)=e_\ell((a_p(k))_p).
$$

#### 证明

将 \(E_{\ell,\le m}\) 展开为

$$
E_{\ell,\le m}(b)
=\sum_{\substack{D\le m\\D\mid b}}\beta_D,
\qquad \beta_D\ge0.
$$

于是

$$
\begin{aligned}
\sum_{b\in I}E_{\ell,\le m}(b)
&=\sum_{D\le m}\beta_DN_I(D)\\
&\le\sum_{D\le m}\beta_D\left(\frac mD+1\right)\\
&\le 2m\sum_{D\le m}\frac{\beta_D}{D}\\
&\le 2m\,e_\ell((h_p)_p)
\le\frac{2mH^\ell}{\ell!}.
\end{aligned}
$$

这里 \(D\le m\) 正好把所有 \(+1\) 吸收到 \(m/D\) 中。

若 \(k\le m\)，任何出现在 \(e_\ell(a_p(k))\) 中的乘积 \(D\) 都整除 \(k\)，从而 \(D\le k\le m\)，所以没有被截去。证毕。

这修正了 A1 中的“模数个数可能超过 \(m\)”问题，但下面的反例说明：即使热点只有一个，这些矩估计仍不足以保证 \(W\ge L\)。

---

# 3. 反射窗口：核心对抗结构

## 引理 3 [PROVED]：反射窗口证书上界

取 \(n\ge2\) 个不同素数

$$
\mathcal P=\{p_1<p_2<\cdots<p_n\},
$$

并取整数 \(m\ge p_1p_2\)。定义仅有的非零 atoms 为

$$
\alpha_{p,1}=1\qquad(p\in\mathcal P).
$$

因此

$$
S_0(u)=\omega_{\mathcal P}(u)
:=|\{p\in\mathcal P:p\mid u\}|.
$$

令

$$
B:=m!,\qquad
x:=B-m,\qquad
I=\{B-m+1,\ldots,B\}.
$$

置

$$
Y:=\left\lfloor\frac{m}{p_1p_2}\right\rfloor .
$$

则

$$
\boxed{W(I)\le Y(n-1).}
$$

### 证明：原 LP 侧

对 \(D\le m\)，定义

$$
r(D):=\omega_{\mathcal P}(D).
$$

因为 \(D\mid m!=B\)，对 \(D<m\) 有

$$
D\mid B-D.
$$

同时，对任意 \(p\in\mathcal P\),

$$
p\mid B-D\iff p\mid D,
$$

故

$$
S_0(B-D)=r(D).
$$

若 \(D<m\) 且 \(r(D)\le1\)，则点 \(B-D\in I\) 的容量为零：

$$
h_1(S_0(B-D))=(r(D)-1)^+=0.
$$

任意可行证书均满足

$$
0\le c_D
\le
\sum_{E\mid B-D}c_E
\le0,
$$

从而

$$
c_D=0.
\tag{3.1}
$$

因此，除可能的 \(D=m\) 外，所有可具有正系数的模数都满足 \(r(D)\ge2\)，进而

$$
D\ge p_1p_2,
\qquad
\left\lfloor\frac mD\right\rfloor\le Y.
\tag{3.2}
$$

若 \(D=m\)，则目标乘子为 \(1\le Y\)。

另一方面，所有 \(D\le m\) 都整除 \(B\)，而

$$
S_0(B)=n.
$$

所以点 \(B\) 的可行性约束给出

$$
\sum_{D\le m}c_D\le n-1.
\tag{3.3}
$$

结合 (3.1)–(3.3)：

$$
\sum_{D\le m}c_D\left\lfloor\frac mD\right\rfloor
\le
Y\sum_{D\le m}c_D
\le Y(n-1).
$$

对所有可行 \(c\) 取上确界即得结论。证毕。

---

## 引理 4 [PROVED]：对应的显式低费用对偶 cover

在引理 3 的窗口中定义

$$
y_B:=Y,
$$

并对 \(1\le t<m\) 定义

$$
y_{B-t}:=
\begin{cases}
m,&\omega_{\mathcal P}(t)\le1,\\
0,&\omega_{\mathcal P}(t)\ge2.
\end{cases}
$$

则 \(y\) 是窗口 LP 的对偶可行解，且费用恰为

$$
\sum_{b\in I}y_bh_1(S_0(b))=Y(n-1).
$$

### 证明

固定 \(D\le m\)。

若 \(r(D)\ge2\)，则 \(D\ge p_1p_2\)，且 \(D\mid B\)，故

$$
\sum_{\substack{b\in I\\D\mid b}}y_b
\ge y_B=Y
\ge\left\lfloor\frac mD\right\rfloor.
$$

若 \(r(D)\le1\) 且 \(D<m\)，则 \(D\mid B-D\)，并且

$$
y_{B-D}=m
\ge\left\lfloor\frac mD\right\rfloor.
$$

最后若 \(D=m\)，则 \(y_B=Y\ge1=\lfloor m/D\rfloor\)。

因此所有对偶约束成立。

除 \(B\) 外，所有具有正 \(y\) 的点都满足 \(S_0\le1\)，费用为零；在 \(B\) 处费用为

$$
Y(S_0(B)-1)=Y(n-1).
$$

证毕。

这已经直接给出一个可能低于 \(L_C\) 的 fractional cover，因而可直接反驳 T2。

---

# 4. 初始区间中的组合爆炸

## 引理 5 [PROVED]：高点下界

设 \(C\ge2\)，令

$$
r:=C+1.
$$

若

$$
m\ge p_{n-r+1}p_{n-r+2}\cdots p_n,
$$

则

$$
\boxed{L_C\ge {n\choose r}.}
$$

### 证明

对每个 \(r\)-元子集 \(A\subseteq\mathcal P\)，取

$$
k_A:=\prod_{p\in A}p.
$$

这些整数由唯一分解定理两两不同，且 \(k_A\le m\)。此外

$$
S_0(k_A)=r=C+1,
$$

所以

$$
h_C(S_0(k_A))=1.
$$

共有 \(\binom nr\) 个这样的 \(k_A\)。证毕。

---

## 定理 6 [PROVED]：有限的通用障碍判据

在引理 3–5 的条件下，如果

$$
{n\choose C+1}
>
(n-1)\left\lfloor\frac m{p_1p_2}\right\rfloor,
\tag{6.1}
$$

则

$$
\boxed{W(I)<L_C.}
$$

然而同一个窗口满足

$$
\boxed{R\ge L_C+C-1.}
\tag{6.2}
$$

### 证明

第一式由引理 3 和引理 5 立即得到。

证明 (6.2)。窗口点可以写成

$$
B-t,\qquad 0\le t<m.
$$

对 \(1\le t<m\),

$$
S_0(B-t)=S_0(t).
$$

因此

$$
R=
\sum_{t=1}^{m-1}h_1(S_0(t))+h_1(n),
$$

而

$$
L_C=
\sum_{t=1}^{m-1}h_C(S_0(t))+h_C(S_0(m)).
$$

第一部分逐点有

$$
h_1(S_0(t))\ge h_C(S_0(t)).
$$

又因为 \(S_0(m)\le n\) 且 \(n\ge C+1\)，

$$
h_1(n)-h_C(S_0(m))
\ge (n-1)-(n-C)=C-1.
$$

所以 \(R-L_C\ge C-1\)。证毕。

这说明失败完全来自证书 cone，而不是原始不等式。

---

# 5. 原始阈值 \(64\) 的无限反例族

下面只使用一个初等素数丰度估计。

## 引理 7 [PROVED]：所需的初等素数上界

令

$$
n=2^s,\qquad s\ge2048.
$$

则第 \(2n\) 个素数满足

$$
p_{2n}\le 10ns.
$$

### 证明

令

$$
u:=5ns.
$$

中央二项式系数满足

$$
\frac{4^u}{2u+1}\le {2u\choose u}.
\tag{7.1}
$$

另一方面，写

$$
{2u\choose u}=\prod_{p\le2u}p^{e_p}.
$$

由 Legendre 公式，

$$
e_p
=
\sum_{j\ge1}
\left(
\left\lfloor\frac{2u}{p^j}\right\rfloor
-
2\left\lfloor\frac{u}{p^j}\right\rfloor
\right).
$$

每个括号为 \(0\) 或 \(1\)，故

$$
e_p\le\lfloor\log_p(2u)\rfloor,
\qquad
p^{e_p}\le2u.
$$

因此

$$
{2u\choose u}\le(2u)^{\pi(2u)}.
\tag{7.2}
$$

由 (7.1)–(7.2)，

$$
\pi(2u)
\ge
\frac{u\log4-\log(2u+1)}{\log(2u)}.
\tag{7.3}
$$

因为 \(s\ge2048\)，

$$
10s\le 2^s=n,
$$

从而

$$
2u=10ns\le n^2,
\qquad
\log(2u)\le2\log n<2s.
$$

又有 \(\log4>1\)，故 (7.3) 的第一项大于

$$
\frac{u}{2s}
=
\frac{5ns}{2s}
=\frac52n.
$$

而

$$
\frac{\log(2u+1)}{\log(2u)}<2.
$$

于是

$$
\pi(2u)>\frac52n-2>2n.
$$

因此前 \(2n\) 个素数全部不超过 \(2u=10ns\)。证毕。

---

## 定理 8 [PROVED — T3]：\(C=64\) 的无限窗口 LP 失败族

对每个整数 \(t\ge11\)，定义

$$
s_t:=2^t,\qquad
n_t:=2^{s_t}.
$$

令 \(p_j\) 表示第 \(j\) 个素数，并取

$$
\mathcal P_t
:=
\{p_{n_t+1},p_{n_t+2},\ldots,p_{2n_t}\}.
$$

写

$$
q_t:=p_{2n_t},
\qquad
m_t:=q_t^{65},
\qquad
B_t:=m_t!,
\qquad
x_t:=B_t-m_t.
$$

仅取 atoms

$$
\alpha_{p,1}=1\quad(p\in\mathcal P_t).
$$

则该实例满足原始全部假设，并且

$$
\boxed{W(x_t)<L_{64}.}
$$

更强地，

$$
\boxed{
\frac{W(x_t)}{L_{64}}
\le
\frac{20^{65}\,65!\,s_t^{65}}{n_t}
\longrightarrow0.
}
\tag{8.1}
$$

### 假设核验

共有 \(n_t\) 个 atoms。因为

$$
p_{n_t+1}\ge n_t+2,
$$

所以

$$
H
=
\sum_{p\in\mathcal P_t}\frac1p
\le
\frac{n_t}{n_t+2}
<1<\frac{17}{16}.
$$

又因为 \(q_t\le m_t/64\) 对如此大的 \(q_t\) 显然成立：

$$
\frac{m_t}{q_t}=q_t^{64}\ge64.
$$

故 support 条件也满足。

### \(W\) 的上界

由引理 7，

$$
q_t\le10n_ts_t.
$$

两个最小所选素数的乘积大于 \(n_t^2\)。引理 3 因而给出

$$
\begin{aligned}
W(x_t)
&\le
(n_t-1)
\left\lfloor
\frac{q_t^{65}}
{p_{n_t+1}p_{n_t+2}}
\right\rfloor\\
&<
\frac{q_t^{65}}{n_t}\\
&\le
10^{65}n_t^{64}s_t^{65}.
\end{aligned}
\tag{8.2}
$$

### \(L_{64}\) 的下界

任何 65 个所选素数的乘积都不超过 \(q_t^{65}=m_t\)，故引理 5 给出

$$
L_{64}\ge {n_t\choose65}.
$$

由于 \(n_t\ge130\)，

$$
{n_t\choose65}
\ge
\frac{(n_t/2)^{65}}{65!}
=
\frac{n_t^{65}}{2^{65}65!}.
\tag{8.3}
$$

由 (8.2)–(8.3)，

$$
\frac{W(x_t)}{L_{64}}
\le
\frac{20^{65}65!s_t^{65}}{n_t}.
$$

最后验证该量小于 \(1\)。因为

$$
20^{65}<2^{325},\qquad
65!<128^{65}=2^{455},
\qquad
s_t^{65}=2^{65t},
$$

所以

$$
20^{65}65!s_t^{65}
<
2^{780+65t}.
$$

而

$$
n_t=2^{2^t}.
$$

当 \(t=11\) 时

$$
2^t=2048>780+65\cdot11=1495.
$$

此后左侧指数每步至少增加 \(2^t\)，右侧只增加 \(65\)，故对所有 \(t\ge11\),

$$
n_t>20^{65}65!s_t^{65}.
$$

因此 \(W(x_t)<L_{64}\)，且比值趋于零。证毕。

---

## 推论 9 [PROVED]：无限族只有一个热点

对定理 8 的族，

$$
\{b\in I:S_0(b)>72\}=\{B_t\}.
$$

### 证明

由上面的增长条件尤其有

$$
n_t>(10s_t)^{65}.
$$

若 \(1\le u\le m_t\) 被至少 66 个所选素数整除，则

$$
u\ge(n_t+2)^{66}>n_t^{66}.
$$

但

$$
m_t=q_t^{65}
\le(10n_ts_t)^{65}
=n_t^{65}(10s_t)^{65}
<n_t^{66},
$$

矛盾。因此 \(S_0(u)\le65\) 对所有 \(u\le m_t\) 成立。

窗口中除 \(B_t\) 外的点均为 \(B_t-u\)，其 \(S_0\) 值等于 \(S_0(u)\le65\)。而

$$
S_0(B_t)=n_t>72.
$$

证毕。

所以 A2 的困难不是“很多热点”；**一个**真实的 LCM-rich 热点就足以让整个窗口 LP 失效。

---

# 6. 精确的缩放阈值 \(C=2\) 有限见证

## 定理 10 [PROVED — exact finite computation]

令 \(\mathcal P\) 为闭区间

$$
[3299,6899]
$$

内的所有素数。精确枚举给出：

$$
|\mathcal P|=425,
$$

两个最小素数为

$$
3299,\ 3301,
$$

三个最大素数为

$$
6871,\ 6883,\ 6899.
$$

取

$$
m:=6871\cdot6883\cdot6899
=326\,275\,048\,607,
$$

$$
B:=m!,\qquad I=(B-m,B].
$$

令 \(S_0(u)=\omega_{\mathcal P}(u)\)，并把左侧阈值改为 \(C=2\)。

则

$$
Y=
\left\lfloor
\frac{m}{3299\cdot3301}
\right\rfloor
=29960.
$$

由引理 3，

$$
W(I)
\le29960\cdot424
=12\,703\,040.
$$

另一方面，每个所选素数三元组的乘积都不超过三个最大素数的乘积 \(m\)，故

$$
L_2
\ge {425\choose3}
=12\,704\,100.
$$

所以

$$
\boxed{
W(I)\le12\,703\,040
<
12\,704\,100
\le L_2.
}
$$

严格差额为

$$
1060.
$$

同时

$$
H\le\frac{425}{3299}<\frac{17}{16},
$$

并且所有所选素数均远小于 \(m/64\)。

因此这是一个不需要浮点数、不需要 SciPy 容差、也不需要枚举 \(m\) 行 LP 的**精确有限对偶见证**。它说明任何 T4 型结论若覆盖 \(C=2\) 且上界至少达到

$$
326\,275\,048\,607
$$

就必定为假。较小的有限验证范围不受此反例影响。

---

# 7. 抽象多重集与 residue-defined window 的对抗检查

## 检查 A [PROVED]：不是抽象 projective-plane 假象

该障碍在抽象 incidence 语言中是：

1. 有一个热点行 \(B\)，包含所有模数 \(D\le m\)，容量 \(n-1\)；
2. 每个只含至多一个所选素数的 \(D<m\)，都有一个容量为零的行阻断它；
3. 所有未被阻断的模数都含至少两个所选素数，因此其目标乘子至多 \(Y\)。

于是任何证书价值至多 \(Y(n-1)\)。

反射点

$$
B-D=m!-D
$$

把这一抽象结构在整数窗口中**同时精确实现**。所用的目标权重正是实际的

$$
\left\lfloor\frac mD\right\rfloor,
$$

不是任意 base counts。

---

## 检查 B [PROVED]：允许所有模数仍无法逃脱

上界并没有把 \(D\) 限制为：

* 高点的除数；
* atom 产品；
* pair/triple/shadow 模数；
* squarefree 模数。

它覆盖所有 \(D\le m\)。

若 \(D<m\) 只含至多一个所选素数，则 \(c_D=0\)。若它含至少两个，则 \(D\ge p_1p_2\)，目标乘子至多 \(Y\)。点 \(B=m!\) 又同时约束所有 \(D\le m\)。

因此添加任意辅助因子、改变 shadow 分组、使用高阶模数，都不能突破该上界。

---

## 检查 C [PROVED]：实际稀疏核没有失败

这些窗口满足

$$
R\ge L_{64}+63
$$

或在缩放实例中满足

$$
R\ge L_2+1.
$$

所以这里没有把 LP 失败误判为 \((SC_C)\) 失败。

其根源是：\(W\)-证书给同一模数 \(D\) 的所有倍数赋予同一个非负系数；而实际 \(R\) 可以逐点利用窗口中反射出来的大量中等重叠。

---

# 8. 对 A1–A3 的判决

### A1：热点矩估计

**[PROVED，正确但不足]**

$$
|T_{72}|<\frac{1105}{73728}m
$$

以及截断高阶矩的 \(2mH^\ell/\ell!\) 上界均成立。

但反例族中 \(|T_{72}|=1\)，所以“小热点集”本身不能控制证书损失。

### A2：cold pair + hot shadow

**[PROVED — refuted as a universal strategy]**

反例窗口中所有冷点确实很冷，只有终点 \(B\) 热。但 \(B\) 同时整除所有 \(D\le m\)，产生约束

$$
\sum_{D\le m}c_D\le n-1.
$$

低 atom-rank 模数又被冷反射点逐个归零。因而任何 pair、triple、shadow 混合证书都受同一上界 \(Y(n-1)\) 控制。

### A3：LCM-rich 热窗口是模型对手

**[PROVED，且给出精确实现]**

最坏模型正是

$$
I=(m!-m,m!].
$$

这不是数值猜测，而是得到 \(W<L\) 无限族的精确结构。

---

# 9. Lean 形式化所需内容

不需要形式化通用 LP 强对偶；使用弱对偶或直接 primal 上界即可。

核心模块如下。

1. **反射整除**

   $$
   D\le m\Longrightarrow D\mid m!,
   $$

   以及

   $$
   p\mid m!\Longrightarrow
   \bigl(p\mid(m!-D)\iff p\mid D\bigr).
   $$

2. **零容量强制**
   从

   $$
   c_E\ge0,\qquad
   \sum_{E\mid b}c_E\le0
   $$

   推出每个 \(E\mid b\) 的 \(c_E=0\)。

3. **唯一分解**
   不同素数子集的乘积不同，并且一个 \(r\)-元子集乘积恰有 \(r\) 个所选素因子。

4. **有限和上界**

   $$
   \sum_D c_D\lfloor m/D\rfloor
   \le
   Y\sum_Dc_D.
   $$

5. **中央二项式素数计数**

   * \(\binom{2u}{u}\ge4^u/(2u+1)\)；
   * \(v_p\binom{2u}{u}\le\lfloor\log_p(2u)\rfloor\)；
   * 因而 \(\binom{2u}{u}\le(2u)^{\pi(2u)}\)。

6. **有限 \(C=2\) 数据**
   区间 \([3299,6899]\) 的素数枚举和整数乘法可由 `native_decide` 或反射后的 primality certificates 完成。

完整证明不需要构造 \(m!\) 的数值，只需使用 `Nat.factorial` 的整除性质。

---

# 10. 可复算材料

精确验证器只使用 Python 标准库和整数运算：

* [round14_window_lp_obstruction.py](sandbox:/mnt/data/round14_window_lp_obstruction.py)
* [精确运行输出](sandbox:/mnt/data/round14_window_lp_obstruction_output.txt)

SHA-256：

```text
960843859940d516bb801a0516d7b346c7d79643622902356f0c88359c93712e  round14_window_lp_obstruction.py
a0c952eab261b0efbe189699f8fd968a19bccc049752eb1502ec2010ff692a35  round14_window_lp_obstruction_output.txt
```

---

# 最终依赖图

$$
\boxed{
\text{T3：存在无限多 }W<L_{64}
}
$$

$$
\longleftarrow
\begin{cases}
\text{反射窗口证书上界 }W\le(n-1)\lfloor m/(p_1p_2)\rfloor,\\
\text{65-素数子集下界 }L_{64}\ge\binom n{65},\\
\text{中央二项式给出的 }p_{2n}\le10ns,\\
n=2^{2^t}\text{ 的显式增长比较}.
\end{cases}
$$

由此：

$$
\boxed{\text{T2 false}}
\quad\longleftarrow\quad
\text{显式对偶 cover }y\text{ 的费用}<L.
$$

$$
\boxed{\text{T1 中的“每窗价值}\ge L\text{证书” false}}
\quad\longleftarrow\quad
W<L.
$$

$$
\boxed{
C=2\text{ 精确有限 LP 失败于 }
m=326\,275\,048\,607
}
$$

$$
\longleftarrow
\binom{425}{3}
>
424\left\lfloor
\frac{326\,275\,048\,607}{3299\cdot3301}
\right\rfloor.
$$

**本轮未证明项：**

$$
(SC_{64})\text{ 对任意窗口的真实不等式}
$$

既没有被上述族反驳，也不能再通过当前的非负除数证书 LP 来完成；上述族反而满足 \(R\ge L+63\)。下一条可行路线必须离开“一个系数 \(c_D\) 同时作用于窗口中全部 \(D\)-倍数”的证书 cone，例如允许按倍数位置或 residue class 区分的运输/匹配结构。
