## 结论

设

$$
L:=\sum_{k\le m}(S_0(k)-64)^+,\qquad
R:=\sum_{b\in I}(S_0(b)-1)^+,
$$

并记

$$
c_0:=6.24\cdot10^{-90},\qquad
C_*:=\frac{32}{3}\bigl(1-6^{-31}\bigr).
$$

本轮得到三项严格结论：

1. **[PROVED]**

   $$
   L>0\quad\Longrightarrow\quad
   R\ge C_*\,m^{31/32}.
   $$

   更精确地，若 \(S_0(k)>64\)，则

   $$
   R\ge C_*\,\frac{m}{k^{1/32}}.
   $$

2. **[PROVED]**

   $$
   4096<m\le 10^{2887}\quad\Longrightarrow\quad (SC_{64}).
   $$

   这是完整的、对所有实数权重 \(\alpha_{p,j}\) 有效的结论。

3. **[PROVED — A2 REFUTED]**
   “把每个高点 \(k\) 只收费给窗口内的 \(k\)-倍数”的 A2 方案，会在真实的单一残数窗口中以任意大因子超载；不仅平均收费失败，任何仅使用这些倍数的流都失败。不过该构造不是 \((SC_{64})\) 反例：其中真实的 \(R/L\) 反而至少为 \(64(M+1)^{63}\)。

以下给出完整证明。

---

## 1. 三十二组装箱引理

### Lemma 1 — [PROVED]

设 \(x_1,\dots,x_N\in(0,1]\)，且

$$
\sum_{i=1}^N x_i>64.
$$

则可以构造两两不交的指标集

$$
G_1,\dots,G_{32}\subseteq\{1,\dots,N\},
$$

使得对每个 \(r\le32\)，

$$
\frac43<\sum_{i\in G_r}x_i\le2.
$$

#### 构造

称 \(x_i>2/3\) 的项为大项。

若大项至少有 \(64\) 个，任取其中 \(64\) 个，两两配对。每对的和严格大于 \(4/3\)，且不超过 \(2\)。

以下设大项数为 \(\ell\le63\)。先将其中 \(2\lfloor\ell/2\rfloor\) 个两两配对。这给出

$$
s:=\lfloor\ell/2\rfloor
$$

个合格组，每组质量不超过 \(2\)。

还需构造

$$
r:=32-s
$$

个组。删除已经配对的大项后，剩余总质量严格大于

$$
64-2s=2r.
$$

若 \(\ell\) 为奇数，剩余项中还有一个大项；以它开始第一组，然后依次加入小项，直到组质量第一次严格超过 \(4/3\)。若 \(\ell\) 为偶数，直接从小项开始。其后各组均采用同一贪心规则。

在每个贪心组中，最后加入的项不超过 \(2/3\)，而加入前的质量不超过 \(4/3\)，所以每个完成组的质量不超过 \(2\)。

完成前 \(j<r\) 个组后至多消耗 \(2j\)，故剩余质量严格大于

$$
2r-2j=2(r-j)>\frac43.
$$

所以过程必能完成全部 \(r\) 个组。证毕。

#### 对抗检查

这是纯有限组合引理，对抽象多重集和真实算术实例都成立。严格不等号没有被极限或数值近似代替。

---

## 2. 一个高点产生三十二个算术影子

对每个素数 \(p\)，记

$$
a_p(n):=\sum_{j:p^j\mid n}\alpha_{p,j}.
$$

于是

$$
S_0(n)=\sum_p a_p(n),\qquad 0\le a_p(n)\le1.
$$

### Lemma 2 — [PROVED]

若某个 \(k\le m\) 满足

$$
S_0(k)>64,
$$

则存在两两互素的整数

$$
D_1,\dots,D_{32}\ge6
$$

满足

$$
\prod_{i=1}^{32}D_i\mid k
$$

以及逐点证书

$$
\boxed{\qquad
\frac13\sum_{i=1}^{32}\mathbf 1[D_i\mid n]
\le (S_0(n)-1)^+
\qquad}
\tag{2.1}
$$

对每个正整数 \(n\) 均成立。

因而对任意长度为 \(m\) 的整数窗口 \(I\)，

$$
\boxed{\qquad
R\ge
\frac{32}{3}\bigl(1-6^{-31}\bigr)\frac{m}{k^{1/32}}.
\qquad}
\tag{2.2}
$$

#### 证明：构造 \(D_i\)

考虑所有满足 \(a_p(k)>0\) 的素数，以 \(a_p(k)\) 作为 Lemma 1 中的项。其总和为 \(S_0(k)>64\)，故得到三十二个互不相交的素数集合

$$
G_1,\dots,G_{32}
$$

满足

$$
\frac43<\sum_{p\in G_i}a_p(k)\le2.
\tag{2.3}
$$

对每个满足 \(a_p(k)>0\) 的 \(p\)，令

$$
J_p:=\max\{j:\alpha_{p,j}>0,\ p^j\mid k\},
\qquad q_p:=p^{J_p}.
$$

定义

$$
D_i:=\prod_{p\in G_i}q_p.
$$

因为不同组使用互不相同的素数，\(D_i\) 两两互素。又因每个 \(q_p\mid k\)，

$$
\prod_iD_i\mid k.
\tag{2.4}
$$

每个组至少含两个不同素数：单个素数的总贡献不超过 \(1\)，而组质量大于 \(4/3\)。因此

$$
D_i\ge2\cdot3=6.
\tag{2.5}
$$

#### 证明逐点证书

固定 \(n\)，设恰有 \(t\) 个 \(D_i\) 整除 \(n\)。

若 \(D_i\mid n\)，则对每个 \(p\in G_i\)，有 \(q_p\mid n\)，因而所有在 \(k\) 上激活的 \(p\)-原子也在 \(n\) 上激活：

$$
a_p(n)\ge a_p(k).
$$

各组使用的素数不交，所以

$$
S_0(n)>
\frac{4t}{3}.
$$

若 \(t=0\)，(2.1) 显然。若 \(t\ge1\)，则

$$
(S_0(n)-1)^+>
\frac{4t}{3}-1
\ge\frac t3,
$$

因为

$$
\frac{4t}{3}-1-\frac t3=t-1\ge0.
$$

故 (2.1) 成立。

#### 对窗口求和

记

$$
N_I(d):=\#\{b\in I:d\mid b\}.
$$

任意长度为 \(m\) 的窗口都满足

$$
N_I(d)\ge\left\lfloor\frac md\right\rfloor.
\tag{2.6}
$$

由 (2.1)，

$$
R\ge\frac13\sum_{i=1}^{32}N_I(D_i)
\ge\frac13\sum_{i=1}^{32}\left\lfloor\frac m{D_i}\right\rfloor.
\tag{2.7}
$$

由 (2.4)、(2.5)，对每个 \(i\)，

$$
D_i\prod_{j\ne i}D_j\le k\le m,
\qquad
\prod_{j\ne i}D_j\ge6^{31}.
$$

因此

$$
\frac m{D_i}\ge6^{31}.
$$

所以

$$
\left\lfloor\frac m{D_i}\right\rfloor
\ge
\left(1-6^{-31}\right)\frac m{D_i}.
\tag{2.8}
$$

再由 AM–GM，

$$
\sum_{i=1}^{32}\frac1{D_i}
\ge
\frac{32}{(\prod_iD_i)^{1/32}}
\ge
\frac{32}{k^{1/32}}.
\tag{2.9}
$$

将 (2.8)、(2.9) 代入 (2.7)，即得 (2.2)。证毕。

### Corollary 2.1 — [PROVED]

若 \(L>0\)，则

$$
\boxed{\qquad
R\ge C_*m^{31/32},
\qquad
C_*:=\frac{32}{3}(1-6^{-31}).
\qquad}
\tag{2.10}
$$

因为任选一个高点 \(k\le m\)，在 (2.2) 中使用

$$
k^{1/32}\le m^{1/32}.
$$

而且

$$
C_*>\frac{52}{5}=10.4.
\tag{2.11}
$$

事实上

$$
\frac{52}{5}\cdot\frac3{32}=\frac{39}{40},
$$

而 \(6^{31}>40\)，故

$$
1-6^{-31}>\frac{39}{40}.
$$

#### 抽象多重集攻击

Lemma 2 不能在 S4 的抽象关联表中冒用。证明真正使用了：

$$
D_1\cdots D_{32}\mid k\le m,
$$

以及真实窗口中的

$$
N_I(D_i)\ge\lfloor m/D_i\rfloor.
$$

抽象的独立 \(\pm1\) 亏损表没有这些乘法约束。

#### 残数窗口攻击

证明未假定不同模数的残数独立，也没有将各个端点误差独立相加。对每个 \(D_i\) 只使用了任何单一真实窗口都满足的 (2.6)，所以适用于所有 \(x\)。

---

## 3. \((SC_{64})\) 直到 \(10^{2887}\)

### Theorem 3 — [PROVED]

在题设的全部稀疏核条件下，

$$
\boxed{\qquad
4096<m\le10^{2887}
\quad\Longrightarrow\quad
L\le R.
\qquad}
\tag{3.1}
$$

#### 证明

若 \(L=0\)，结论显然。

以下设 \(L>0\)。由 S2，

$$
L<c_0m,
\qquad
c_0=6.24\cdot10^{-90}.
\tag{3.2}
$$

由 Corollary 2.1，

$$
R\ge C_*m^{31/32},
\qquad C_*>\frac{52}{5}.
\tag{3.3}
$$

只需证明

$$
c_0m^{1/32}<\frac{52}{5}.
\tag{3.4}
$$

当 \(m\le10^{2887}\) 时，

$$
m^{1/32}
\le10^{2887/32}
=10^{90}10^{7/32}.
$$

有精确不等式

$$
10^{7/32}<\frac53.
\tag{3.5}
$$

验证如下：

$$
\left(\frac53\right)^8
=\frac{390625}{6561}>59,
$$

故

$$
\left(\frac53\right)^{32}>59^4
=12117361>10^7.
$$

因此

$$
c_0m^{1/32}
<
6.24\cdot10^{-90}\cdot\frac53\cdot10^{90}
=10.4
=\frac{52}{5}.
$$

于是

$$
L<c_0m
<
\frac{52}{5}m^{31/32}
<
C_*m^{31/32}
\le R.
$$

证毕。

更精确的充分范围是

$$
m<
\left(
\frac{\frac{32}{3}(1-6^{-31})}
     {6.24\cdot10^{-90}}
\right)^{32}.
\tag{3.6}
$$

---

## 4. 一个独立的周期算术分支

Lemma 2 处理“大周期、至少有一个高点”的情形。支持集总周期较小时，还有一个完全不同的确定性结论。

设

$$
P:=\#\{p:\exists j,\ \alpha_{p,j}>0\},
$$

并令

$$
Q:=\prod_p p^{J_p},
\qquad
J_p:=\max\{j:\alpha_{p,j}>0\}.
$$

于是 \(S_0(n)\) 以 \(Q\) 为周期。

### Lemma 4 — [PROVED]

令

$$
q:=\left\lfloor\frac mQ\right\rfloor.
$$

若

$$
63q\ge P-64,
\tag{4.1}
$$

则 \((SC_{64})\) 成立。

更精确地，令

$$
U:=\max_{1\le r\le Q}(S_0(r)-64)^+.
$$

条件

$$
63q\ge U
\tag{4.2}
$$

已经足够。

#### 证明

记一个完整周期上的两种和为

$$
L_Q:=\sum_{r=1}^Q(S_0(r)-64)^+,
\qquad
R_Q:=\sum_{r=1}^Q(S_0(r)-1)^+.
$$

令

$$
\mathcal H_Q:=\{r\in[1,Q]:S_0(r)>64\},
\qquad N:=|\mathcal H_Q|.
$$

对每个 \(r\in\mathcal H_Q\)，

$$
(S_0(r)-1)^+-(S_0(r)-64)^+=63.
$$

其他残数的差非负。因此

$$
R_Q-L_Q\ge63N.
\tag{4.3}
$$

任意长度为 \(m=qQ+s\)、\(0\le s<Q\) 的窗口，恰好包含 \(q\) 个完整周期，再加一个长度 \(s\) 的残数块。因此

$$
R_I=qR_Q+R_{\rm rem},
\qquad R_{\rm rem}\ge0.
$$

同理，

$$
L_K=qL_Q+L_{\rm pre},
$$

其中前缀余块最多包含全部 \(N\) 个高残数，所以

$$
L_{\rm pre}\le NU.
$$

故

$$
R_I-L_K
\ge q(R_Q-L_Q)-NU
\ge N(63q-U).
$$

条件 (4.2) 即得结论。

又因为每个素数贡献至多 \(1\)，

$$
S_0(r)\le P,
$$

所以

$$
U\le P-64.
$$

由此得到 (4.1)。证毕。

这覆盖了任意巨大的 \(m\)，只要支持的公共周期 \(Q\) 相对于 \(m\) 足够小。例如固定有限支持时，\(m/Q\) 最终必满足该条件。

---

## 5. 0/1 情形的更强单点影子

### Lemma 5 — [PROVED]

设所有非零权重均为 \(1\)，支持在一个素数集合 \(\mathcal P\) 上。若某个 \(k\le m\) 满足

$$
\omega_{\mathcal P}(k)\ge65,
$$

则

$$
\boxed{\qquad
R\ge
32(1-6^{-31})\frac{m}{k^{2/65}}.
\qquad}
\tag{5.1}
$$

#### 证明

选取 \(k\) 的 \(65\) 个不同的支持素因子

$$
q_1<\cdots<q_{65},
\qquad Q:=\prod_{i=1}^{65}q_i\mid k.
$$

因最大项不小于几何平均数，

$$
q_{65}\ge Q^{1/65}.
$$

故

$$
Q':=\prod_{i=1}^{64}q_i
=\frac Q{q_{65}}
\le Q^{64/65}
\le k^{64/65}.
\tag{5.2}
$$

将前 \(64\) 个素数配成 \(32\) 对，记每对之积为

$$
E_1,\dots,E_{32}.
$$

它们两两互素，且

$$
\prod_iE_i=Q'.
$$

若 \(t\) 个 \(E_i\) 整除 \(b\)，则至少有 \(2t\) 个支持素数整除 \(b\)，所以

$$
(\omega_{\mathcal P}(b)-1)^+
\ge2t-1\ge t.
$$

因此

$$
\sum_i\mathbf1[E_i\mid b]
\le(\omega_{\mathcal P}(b)-1)^+.
$$

与 Lemma 2 相同，每个 \(E_i\ge6\)，故

$$
N_I(E_i)\ge(1-6^{-31})\frac m{E_i}.
$$

AM–GM 与 (5.2) 给出

$$
\sum_i\frac1{E_i}
\ge\frac{32}{(Q')^{1/32}}
\ge\frac{32}{k^{2/65}}.
$$

求和即得 (5.1)。证毕。

这是一个真正的算术 charging lemma，但它仍是“一个高点的全部低阶影子”，不是把所有高点分别收费给其自身倍数。因此它没有落入下面的反例。

---

## 6. A2 的 full-multiple charging 以无界因子失败

### Proposition 6 — [PROVED — T3]

对任意整数 \(M\ge64\)，存在满足全部稀疏核条件的 0/1 实例和一个真实窗口 \(I\)，使得至少

$$
\left\lceil\frac M2\right\rceil
$$

个高点 \(k\) 在 \(I\) 中各自只有同一个可收费倍数 \(B\)。

所以任何只允许高点 \(k\) 向窗口内的 \(k\)-倍数收费的方案，在 \(B\) 处的超载因子至少为

$$
\frac{\lceil M/2\rceil}{64},
$$

随 \(M\to\infty\) 无界。

#### 可重运行的构造

给定 \(M\ge64\)：

1. 依次取大于 \(M\) 的最小 \(65\) 个素数

   $$
   q_1<\cdots<q_{65}.
   $$
2. 令

   $$
   a:=\prod_{i=1}^{65}q_i,\qquad m:=aM.
   $$
3. 取

   $$
   \alpha_{q_i,1}=1
   $$

   且所有其他原子权重为零。
4. 令

   $$
   B:=a\operatorname{lcm}(1,2,\dots,M),
   $$

   并取

   $$
   x:=B-\left\lceil\frac m2\right\rceil.
   $$

   因此

   $$
   I=
   \left\{
   B-\left\lceil\frac m2\right\rceil+1,\dots,
   B+\left\lfloor\frac m2\right\rfloor
   \right\}.
   $$

#### 稀疏条件核验

因为 \(q_i>M\)，

$$
H=\sum_{i=1}^{65}\frac1{q_i}
<\frac{65}{M}
\le\frac{65}{64}
<\frac{17}{16}.
$$

又因 \(q_i\le a\) 且 \(M\ge64\)，

$$
q_i\le a\le\frac{aM}{64}=\frac m{64}.
$$

所以支持条件成立。

#### 高点及唯一倍数

对

$$
t=\left\lfloor\frac M2\right\rfloor+1,\dots,M
$$

令

$$
k_t:=at.
$$

则 \(k_t\le m\)，且所有 \(65\) 个 \(q_i\) 均整除 \(k_t\)，所以

$$
S_0(k_t)=65,\qquad (S_0(k_t)-64)^+=1.
$$

因为 \(t\mid\operatorname{lcm}(1,\dots,M)\)，

$$
k_t\mid B.
$$

同时 \(k_t>m/2\)。故相邻的其他 \(k_t\)-倍数

$$
B-k_t,\qquad B+k_t
$$

均落在 \(I\) 之外。于是 \(B\) 是 \(I\) 中唯一的 \(k_t\)-倍数。

此外

$$
\left\lfloor\frac m{k_t}\right\rfloor
=
\left\lfloor\frac Mt\right\rfloor=1.
$$

因此 A2 所建议的 \(\lfloor m/k_t\rfloor^{-1}\) 权重就是 \(1\)。

所有

$$
M-\left\lfloor\frac M2\right\rfloor
=\left\lceil\frac M2\right\rceil
$$

个单位需求都被强制送到 \(B\)。

由于 \(q_i>M\)，这些素数不整除 \(\operatorname{lcm}(1,\dots,M)\)，故

$$
S_0(B)=65.
$$

而 \(B\) 的 RHS 容量仅为

$$
(S_0(B)-1)^+=64.
$$

命题得证。

这同时反驳了任何形如

$$
\text{“接收重数由 }S_0(B)-65\text{ 控制”}
$$

的估计：这里

$$
S_0(B)-65=0,
$$

但接收重数趋于无穷。

---

## 7. 上述构造不是 \((SC_{64})\) 反例

### Lemma 7 — [PROVED]

在 Proposition 6 的实例中，

$$
L=M,
$$

而

$$
\boxed{\qquad
R\ge64M(M+1)^{63}.
\qquad}
\tag{7.1}
$$

所以

$$
\frac RL\ge64(M+1)^{63}.
$$

#### 证明

这里只有 \(65\) 个支持素数。一个 \(k\le m\) 满足 \(S_0(k)>64\)，当且仅当

$$
a\mid k.
$$

区间 \([1,m]\) 中恰有 \(M\) 个 \(a\)-倍数，每个左侧贡献为 \(1\)，故

$$
L=M.
$$

对 \(b\in I\)，令

$$
r_b:=\#\{i:q_i\mid b\}\le65.
$$

逐点有

$$
(r_b-1)^+
\ge\frac2{65}\binom{r_b}{2}.
\tag{7.2}
$$

当 \(r_b=0,1\) 两边均为零；当 \(2\le r_b\le65\) 时，(7.2) 等价于

$$
\frac{r_b}{65}\le1.
$$

求和得到

$$
R\ge\frac2{65}\sum_{i<j}N_I(q_iq_j).
$$

因为 \(q_iq_j\mid m\)，

$$
N_I(q_iq_j)
\ge\left\lfloor\frac m{q_iq_j}\right\rfloor
=\frac m{q_iq_j}
=M\prod_{\ell\ne i,j}q_\ell.
$$

而所有 \(q_\ell\ge M+1\)，故

$$
\begin{aligned}
R
&\ge
\frac{2M}{65}
\sum_{i<j}\prod_{\ell\ne i,j}q_\ell\\
&\ge
\frac{2M}{65}
\binom{65}{2}(M+1)^{63}\\
&=64M(M+1)^{63}.
\end{aligned}
$$

证毕。

这揭示了 A2 失败的确切原因：**把整个高点模数 \(k\) 当作收费邻域，会把与 \(S_0\) 无关的因子 \(t\) 错误地保留下来；真正提供 RHS 的是大量低阶共同因子 \(q_iq_j\) 及更一般的组影子。**

---

## 8. 独立审稿检查

### 8.1 [PROVED] 没有非法汇总局部证书

Lemma 2 对每个高点 \(k\) 构造一个局部证书

$$
\Phi_k(b):=\frac13\sum_{i=1}^{32}\mathbf1[D_{k,i}\mid b]
\le(S_0(b)-1)^+.
$$

本证明只选取一个高点，因此没有进行错误的

$$
\sum_k\Phi_k(b)\le(S_0(b)-1)^+
$$

推断。

这正是剩余困难所在：不同高点的影子可能高度重合，而同一个 RHS 容量不能被重复使用。

### 8.2 [PROVED] Prime-power 嵌套没有被当成独立原子

每个组使用的是素数级贡献 \(a_p(k)\)，并用最高激活幂 \(q_p\) 一次性保证该素数在 \(k\) 上的全部贡献。没有把同一素数的不同幂错误地放入不同独立组。

### 8.3 [PROVED] 端点误差不是独立的 \(\pm1\)

局部影子证明只使用

$$
N_I(d)\ge\lfloor m/d\rfloor.
$$

周期证明使用完整周期的精确残数计数。两者都适用于由同一个 \(x\) 产生的真实窗口，并未允许模数端点误差独立选择。

### 8.4 [PROVED] A2 反例是真实残数窗口

窗口由单个显式整数

$$
x=B-\lceil m/2\rceil
$$

定义。所有唯一倍数结论均由普通整除和窗口端点直接推出，不是抽象关联表。

### 8.5 [PROVED] 所有数值界均为符号证明

关键数值比较仅使用

$$
59^4=12117361>10^7,\qquad 6^{31}>40,
$$

没有使用随机搜索、浮点实验或“检查未找到反例”。

---

## 9. 本轮四个目标的状态

### T1 — [PROVED in explicit regimes]

已证明完整 fractional \((SC_{64})\)：

$$
4096<m\le10^{2887},
$$

以及所有满足周期条件

$$
63\left\lfloor\frac mQ\right\rfloor\ge P-64
$$

的实例。

未覆盖区间被严格缩小到同时满足

$$
m>10^{2887},
\qquad
63\left\lfloor\frac mQ\right\rfloor<P-64
$$

的快速增长支持实例。

### T2 — [PROVED locally, not globally]

0/1 情形获得了真正的低阶 charging：

$$
S_0(k)\ge65
\quad\Longrightarrow\quad
R\ge32(1-6^{-31})\frac{m}{k^{2/65}}.
$$

但不能把所有高点的这些局部证书直接相加。

### T3 — [PROVED for the proposed charging route]

A2 的 full-multiple charging 被真实窗口以无界因子反驳。

没有得到 \((SC_{64})\) 反例；显式失败族反而满足

$$
R/L\ge64(M+1)^{63}.
$$

### T4 — [PROVED partially]

得到两种真正使用算术结构、而不是抽象计数的机制：

$$
\text{高点}\Longrightarrow32\text{ 个互素组影子},
$$

以及

$$
\text{公共周期足够多}\Longrightarrow(SC_{64}).
$$

---

## 10. 精确剩余缺口

当前链条给出的是

$$
L>0
\quad\Longrightarrow\quad
R\ge C_*m^{31/32}.
$$

S2 给出

$$
L<c_0m.
$$

这两者在 \(m\le10^{2887}\) 时闭合，但在线性上界最终会超过单个高点产生的 \(m^{31/32}\) 影子。

因此剩余问题不是再加强 S3，也不是控制一个 \(b\) 接收多少完整 \(k\)-倍数；后者已被 Proposition 6 否定。所需的新引理必须是：

> 对许多不同高点产生的低阶组模数 \(D_{k,i}\)，利用
>
> $$
> \prod_iD_{k,i}\le k,\qquad
> N_I(D_{k,i})\ge\lfloor m/D_{k,i}\rfloor,
> $$
>
> 以及这些模数来自同一个素数—幂原子系统这一事实，证明其大量 residue-class 容量不能全部只在少数高重合点上浪费。

任何逐点地把所有局部证书直接相加的命题都比 \((SC_{64})\) 强，不能被当成无损归约。真正缺的是一个允许避开共同 CRT 点、保留低阶影子总容量的**全局算术聚合估计**。

---

## 11. Lean 形式化所需组件

1. `bin_cover_32`：对有限实数多重集，按 \(>2/3\) 分类并执行上述配对—贪心构造；输出 \(32\) 个互不相交组及区间 \((4/3,2]\)。

2. `active_prime_power`：对有限支持定义

   $$
   J_p=\max\{j:\alpha_{p,j}>0\land p^j\mid k\},
   $$

   并证明 \(q_p\mid n\Rightarrow a_p(n)\ge a_p(k)\)。

3. `group_divisors_coprime`：证明 \(D_i\) 两两互素、

   $$
   \prod_iD_i\mid k,
   \qquad D_i\ge6.
   $$

4. `interval_multiples_lower`：

   $$
   \#\{x+1\le n\le x+m:d\mid n\}
   \ge m/d
   $$

   其中右侧为自然数整除 `Nat.div`，即 \(\lfloor m/d\rfloor\)。

5. `floor_large_ratio`：若 \(y\ge6^{31}\)，则

   $$
   \lfloor y\rfloor\ge(1-6^{-31})y.
   $$

6. 长度为 \(32\) 的 AM–GM：

   $$
   \sum_iD_i^{-1}\ge32(\prod_iD_i)^{-1/32}.
   $$

7. 数值闭合：

   $$
   \left(\frac53\right)^8>59,\quad
   59^4>10^7,\quad
   1-6^{-31}>\frac{39}{40}.
   $$

   均可由 `norm_num` 完成；唯一需要的实分析是正数取 \(32\) 次根的单调性。

8. 周期引理：把任意长度 \(qQ+s\) 的连续整数区间分解为 \(q\) 个完整剩余系加一个长度 \(s\) 的循环残数段。

9. A2 构造：递归选择大于给定界的下一个素数；定义 `lcm (Finset.range (M+1))`；形式化居中窗口中 \(B\) 是所有 \(k_t>m/2\) 的唯一倍数。

10. pair certificate：

    $$
    (r-1)^+\ge\frac2{65}\binom r2
    \quad(0\le r\le65).
    $$

**final claim ← Lemmas 1–7 + S2 ← unproved items:** \((SC_{64})\) 已对 \(m\le10^{2887}\) 及充分周期化支持完全证明；A2 的 full-multiple charging 已被无界反驳；对 \(m>10^{2887}\) 的剩余项是不同高点之低阶算术影子的全局、非逐点聚合。
