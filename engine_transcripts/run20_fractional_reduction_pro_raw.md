# 本轮结论

没有得到完整的 fractional \((\mathrm{TH}_C)\) 证明，也没有得到它的反例。得到的最强严格结果是：

$$
\boxed{
H_{64}(m,z)\ge \frac{17}{16}
\quad\Longrightarrow\quad
\sum_{k\le m}(S(k)-65)^+
\le
\sum_{b\in I}(S(b)-1)^+ .
}
\tag{DTH\(_{65}\)}
$$

其中

$$
S(n)=\sum_p\min(z_pv_p(n),1)
$$

且 \(H_{64}(m,z)\) 是下文定义的“小模数自然均值”。

因此，完整的 absolute-constant 问题被严格压缩到：

$$
\boxed{
H_{64}(m,z)<\frac{17}{16},
\qquad
p^j\le \frac m{64},
}
\tag{Sparse Core}
$$

即一个自然均值仅略高于 \(1\) 的稀疏系统。这个核心仍未闭合。

同时，建议的三种直接 fractionalization 均存在严格障碍：

1. 正系数 dyadic/level-set 组合不可能控制右端，哪怕允许任意常数倍。
2. “0/1 顶点成立 \(\Rightarrow[0,1]^P\) 成立”的一般延拓原则是假的；有一个 9 坐标的整数反例。
3. 任何固定阶 pair–triple 或 bounded-degree pointwise polynomial 都不能处理任意小权重；高阶层次不可省略。

另得到两个互补的显式 fractional certificate：

* random-partition certificate：左侧捕获很好，但有不可忽略的负系数误差；
* sliding-window certificate：全部系数非负，但捕获量受“活跃块碎片数”限制。

二者精确定位了剩余问题：**必须构造一个既有层次化捕获能力、又不产生不可控负支撑误差的证书。**

---

# 一、prime-power 原子化

## Lemma 1 `[PROVED]`：有限原子分解

定义

$$
\alpha_{p,j}
:=
\min(jz_p,1)-\min((j-1)z_p,1)
\qquad(j\ge1).
$$

则

$$
0\le \alpha_{p,j}\le z_p,\qquad
\sum_{j\ge1}\alpha_{p,j}\le1,
$$

并且

$$
\min(z_pv_p(n),1)
=
\sum_{j\ge1}\alpha_{p,j}\,1_{p^j\mid n}.
\tag{1.1}
$$

对固定 \(m\)，令

$$
S_m(n)
:=
\sum_{\substack{p,j\\p^j\le m}}
\alpha_{p,j}\,1_{p^j\mid n}.
\tag{1.2}
$$

则

$$
S_m(k)=S(k)\qquad(k\le m),
\tag{1.3}
$$

而对任意 \(n\),

$$
S_m(n)\le S(n).
\tag{1.4}
$$

因此，为证明原 fractional 不等式，可以删除全部 \(p^j>m\) 的原子：左侧不变，右侧只会减小。

---

# 二、affine baseline certificate

## Lemma 2 `[PROVED]`：基线证书

对任意一组保留的原子，定义

$$
c_1=-1,\qquad c_{p^j}=\alpha_{p,j},
\tag{2.1}
$$

其他 \(c_d=0\)。则对所有 \(n\),

$$
\sum_{d\mid n}c_d=S_m(n)-1\le (S_m(n)-1)^+.
\tag{2.2}
$$

令

$$
B_m:=\sum_{k\le m}S(k)
=
\sum_{\substack{p,j\\p^j\le m}}
\alpha_{p,j}\left\lfloor\frac m{p^j}\right\rfloor .
$$

按照 P3 中统一的 \(V(c)\) 定义，该证书给出

$$
V(c)=B_m-(m+1).
\tag{2.3}
$$

因此：

## Corollary 3 `[PROVED]`：capped-mass criterion

若对某个 \(C\),

$$
\sum_{k\le m}\min(S(k),C)\ge m+1,
\tag{2.4}
$$

则

$$
V(c)\ge \sum_{k\le m}(S(k)-C)^+,
$$

故 \((\mathrm{TH}_C)\) 成立。

证明只是恒等式

$$
B_m-\sum_{k\le m}(S(k)-C)^+
=
\sum_{k\le m}\min(S(k),C).
$$

所以 dense fractional case 的问题变成：证明 capped mass 超过 \(m+1\)。

---

# 三、模数 \(m/64\) 剥离

令

$$
S_0(n)
:=
\sum_{\substack{p,j\\p^j\le m/64}}
\alpha_{p,j}1_{p^j\mid n},
$$

$$
S_1(n):=S_m(n)-S_0(n).
$$

## Lemma 4 `[PROVED]`：大模数原子对 \(k\le m\) 的总贡献至多 1

若 \(m>64^2=4096\)，则对所有 \(k\le m\),

$$
S_1(k)\le1.
\tag{3.1}
$$

### 证明

如果来自两个不同素数 \(p\ne q\) 的大原子 \(p^j,q^\ell>m/64\) 同时活跃，则

$$
p^jq^\ell>\frac{m^2}{64^2}>m,
$$

不可能整除 \(k\le m\)。

因此大原子最多来自同一个素数。一个素数的全部增量满足

$$
\sum_j\alpha_{p,j}\le1,
$$

故 (3.1) 成立。∎

于是

$$
(S(k)-65)^+
\le
(S_0(k)-64)^+.
\tag{3.2}
$$

另一方面，任意区间点 \(b\) 满足

$$
(S_0(b)-1)^+\le(S(b)-1)^+.
\tag{3.3}
$$

所以证明 \(S_0\) 的 \((64,1)\)-hinge 即足以证明原系统的 \((65,1)\)-hinge。

当 \(m\le4096\) 时，

$$
S(k)\le\omega(k)\le\log_2k\le12<65,
$$

故左侧本来就是零。

---

# 四、dense fractional branch

对每个素数定义

$$
h_p
:=
\sum_{\substack{j\\p^j\le m/64}}
\frac{\alpha_{p,j}}{p^j},
$$

并令

$$
H_{64}(m,z):=\sum_p h_p.
\tag{4.1}
$$

注意

$$
h_p\le\frac1p\sum_j\alpha_{p,j}\le\frac1p\le\frac12.
\tag{4.2}
$$

## Lemma 5 `[PROVED]`：dense capped-mass bound

若

$$
H_{64}(m,z)\ge\frac{17}{16},
\tag{4.3}
$$

则

$$
\sum_{k\le m}\min(S_0(k),64)\ge m+1.
\tag{4.4}
$$

### 证明

由每项 \(h_p\le1/2\)，可以按任意固定顺序贪心选择一个素数子集 \(Q\)，使得

$$
\frac{17}{16}
\le
H_Q:=\sum_{p\in Q}h_p
\le
\frac{25}{16}.
\tag{4.5}
$$

定义

$$
T_Q(k)
:=
\sum_{p\in Q}
\sum_{\substack{j\\p^j\le m/64}}
\alpha_{p,j}1_{p^j\mid k}.
$$

显然 \(0\le T_Q(k)\le S_0(k)\)。

### 一阶矩

因为 \(p^j\le m/64\)，故 \(m/p^j\ge64\)，从而

$$
\left\lfloor\frac m{p^j}\right\rfloor
\ge
\frac{63}{64}\frac m{p^j}.
$$

因此

$$
\begin{aligned}
B_Q
:=
\sum_{k\le m}T_Q(k)
&=
\sum_{p\in Q,j}\alpha_{p,j}
\left\lfloor\frac m{p^j}\right\rfloor\\
&\ge
\frac{63}{64}mH_Q\\
&\ge
\frac{1071}{1024}m.
\end{aligned}
\tag{4.6}
$$

### 二阶矩

写 \(U_p(k)\) 为 \(p\) 对 \(T_Q(k)\) 的贡献。因为 \(0\le U_p\le1\),

$$
\sum_{k\le m}U_p(k)^2
\le
\sum_{k\le m}U_p(k)
\le mh_p.
\tag{4.7}
$$

对不同素数 \(p,q\),

$$
\begin{aligned}
\sum_{k\le m}U_p(k)U_q(k)
&=
\sum_{j,\ell}
\alpha_{p,j}\alpha_{q,\ell}
\left\lfloor\frac m{p^jq^\ell}\right\rfloor\\
&\le mh_ph_q.
\end{aligned}
\tag{4.8}
$$

故

$$
\begin{aligned}
\sum_{k\le m}T_Q(k)^2
&\le
mH_Q+2m\sum_{p<q}h_ph_q\\
&\le
m(H_Q+H_Q^2)\\
&\le
\frac{1025}{256}m.
\end{aligned}
\tag{4.9}
$$

### quadratic cap

对所有实数 \(t\ge0\),

$$
\min(t,64)\ge t-\frac{t^2}{256}.
\tag{4.10}
$$

确实：

* 当 \(t\le64\) 时，右侧不超过 \(t\)；
* 当 \(t\ge64\) 时，二次函数 \(t-t^2/256\) 的全局最大值为 \(64\)，在 \(t=128\) 取得。

因此

$$
\begin{aligned}
\sum_{k\le m}\min(T_Q(k),64)
&\ge
B_Q-\frac1{256}\sum_{k\le m}T_Q(k)^2\\
&\ge
\left(
\frac{1071}{1024}
-
\frac{1025}{65536}
\right)m\\
&=
\frac{67519}{65536}m\\
&=
m+\frac{1983}{65536}m.
\end{aligned}
\tag{4.11}
$$

当 \(m>4096\) 时，最后的余量严格大于 \(1\)。又因 \(T_Q\le S_0\),

$$
\sum_{k\le m}\min(S_0(k),64)\ge m+1.
$$

∎

---

## Theorem 6 `[PROVED]`：fractional dense branch，显式常数 \(65\)

若

$$
H_{64}(m,z)\ge\frac{17}{16},
$$

则对所有 \(x\ge0\),

$$
\boxed{
\sum_{k\le m}(S(k)-65)^+
\le
\sum_{b=x+1}^{x+m}(S(b)-1)^+ .
}
$$

### 证明

当 \(m\le4096\) 时左侧为零。

设 \(m>4096\)。由 Lemma 4，

$$
(S(k)-65)^+\le(S_0(k)-64)^+.
$$

对 \(S_0\) 使用 Lemma 2 的 baseline certificate。由 Lemma 5 和 Corollary 3，

$$
V(c)\ge\sum_{k\le m}(S_0(k)-64)^+.
$$

最后

$$
(S_0(b)-1)^+\le(S(b)-1)^+.
$$

应用 counting transfer 即得。∎

---

# 五、精确剩余核心

## Reduction 7 `[PROVED]`

完整的 \((\mathrm{TH}_{65})\) 只剩下以下命题：

> 对 \(m>4096\)，设
>
> $$
> S_0(n)=
> \sum_{\substack{p,j\\p^j\le m/64}}
> \alpha_{p,j}1_{p^j\mid n},
> $$
>
> 且
>
> $$
> \sum_{\substack{p,j\\p^j\le m/64}}
> \frac{\alpha_{p,j}}{p^j}
> <
> \frac{17}{16}.
> $$
>
> 证明
>
> $$
> \sum_{k\le m}(S_0(k)-64)^+
> \le
> \sum_{b\in I}(S_0(b)-1)^+.
> \tag{SC\(_{64}\)}
> $$

若 \((\mathrm{SC}_{64})\) 成立，则由大模数剥离立即得到完整 fractional \((\mathrm{TH}_{65})\)，从而

$$
g(n)\le81n.
$$

因此现在的障碍不再是 \(\log\log m\) 的总调和质量，而是一个非常具体的**近临界稀疏系统**：

$$
\text{自然均值}<1.0625,
\quad
\text{但允许极罕见的 }S(k)\gg1.
$$

---

# 六、level-set / dyadic 路线的严格障碍

## Lemma 8 `[PROVED]`：任何正系数层析都会制造假铰链

设

$$
L(u)
=
\sum_j a_j
\left(
\#\{i:u_i\ge t_j\}-1
\right)^+,
\qquad a_j\ge0.
$$

假设对某个有限常数 \(K\),

$$
L(u)\le K\left(\sum_i u_i-1\right)^+
\quad\text{对所有 }u_i\in[0,1].
\tag{6.1}
$$

则对每个 \(t_j\le1/2\)，必有 \(a_j=0\)。

### 证明

若 \(a_j>0\)，取

$$
u_1=u_2=t_j,\qquad u_i=0\ (i>2).
$$

则

$$
\sum_i u_i=2t_j\le1,
$$

故右端为零；但第 \(j\) 个 level-set 的计数为 \(2\)，所以左端至少为 \(a_j>0\)，矛盾。∎

这不是常数估计不够好，而是**零集不匹配**：

$$
S\le1\quad\Longrightarrow\quad(S-1)^+=0,
$$

而任意正层析都会在两个低权重坐标同时出现时产生正成本。

特别地，\(u=(1/2,1/2)\) 已经否定了 dyadic RHS：

$$
(S-1)^+=0,
$$

但阈值 \(1/2\) 的 0/1 hinge 为

$$
(2-1)^+=1.
$$

因此 route (i) 不能通过任何固定的正系数组合以及任何有限 multiplicative loss 闭合。要使用 level sets，必须加入带符号的高阶抵消。

---

# 七、0/1 顶点不能黑箱延拓到 fractional cube

## Lemma 9 `[PROVED]`：9 坐标的显式反例

取 9 个坐标。定义两个 set systems：

* 左侧：7 个完全相同的全集 \([9]\)；
* 右侧：全部 \(\binom92=36\) 个二元子集，各出现一次。

对任意 0/1 向量，其支撑大小记为 \(t\)。则

$$
L_{\mathrm{bool}}=7(t-4)^+,
$$

而

$$
R_{\mathrm{bool}}=\binom t2.
$$

逐点检查：

$$
\begin{array}{c|ccccc}
t&5&6&7&8&9\\ \hline
7(t-4)&7&14&21&28&35\\
\binom t2&10&15&21&28&36
\end{array}
$$

故所有 cube vertices 都满足

$$
7(t-4)^+\le\binom t2.
\tag{7.1}
$$

但是取

$$
z_1=\cdots=z_9=\frac12.
$$

每个左侧全集的权重为 \(9/2\)，故

$$
L_{\mathrm{frac}}
=
7\left(\frac92-4\right)
=
\frac72.
$$

每个右侧二元组的总权重恰为 \(1\)，所以

$$
R_{\mathrm{frac}}=0.
$$

因此：

$$
\boxed{
\text{所有 0/1 顶点成立}
\;\centernot\Longrightarrow\;
\text{整个 }[0,1]^P\text{ 成立}.
}
$$

这个反例同时否定了以下潜在原则：

* slack 的最小值必在 cube vertices；
* 对所有素数子集成立即可由 convexity 延拓；
* 0/1 Theorem 6 可以作为一个完全黑箱进行 fractionalization。

乘法结构必须被显式使用。该反例中的缺陷是：右侧没有 9 重交，而真正的除数计数会对 9 个模数之积施加额外约束。

---

# 八、随机 rounding 的精确缺陷

## Lemma 10 `[PROVED]`：独立 Bernoulli rounding 的假成本

令 \(B_i\) 独立，且

$$
\Pr(B_i=1)=u_i,\qquad
R=\sum_iB_i,\qquad
S=\sum_i u_i.
$$

则

$$
\mathbb E(R-1)^+
=
S-\Pr(R\ge1)
=
S-1+\prod_i(1-u_i).
\tag{8.1}
$$

因此相对于真实 fractional hinge 的额外成本为

$$
D(u)
=
\prod_i(1-u_i)-(1-S)^+
\ge0.
\tag{8.2}
$$

例如

$$
u_1=u_2=\frac12
$$

时，

$$
(S-1)^+=0,
\qquad
\mathbb E(R-1)^+=\frac14.
$$

这正是 Lemma 12 的独立-rounding 版本。

---

## Lemma 11 `[PROVED]`：依赖 rounding 也不能逐行消除缺陷

取三个坐标，权重均为 \(1/2\)，并取三条右侧行

$$
\{1,2\},\qquad\{1,3\},\qquad\{2,3\}.
$$

若某个联合 rounding 保持每个坐标的边缘概率 \(1/2\)，并要求三条行的期望 0/1 hinge 均为零，则任何两个坐标都不能同时被选中。

因此被选坐标集必须几乎必然是三角形 \(K_3\) 的独立集，故其大小至多为 \(1\)。但边缘概率要求

$$
\mathbb E|\widehat P|=\frac32,
$$

矛盾。

所以，即使允许任意依赖结构，也不存在一个保持边缘概率、并逐行消除 false hinges 的 rounding。

---

# 九、直接 pair–triple ansatz 的边界

## Lemma 12 `[PROVED]`：正 pair term 对低总权重不可能

设一个 direct certificate 在只有两个坐标 \(u,v\) 活跃时保留正 pair term

$$
A(u,v)>0.
$$

若 \(u+v\le1\)，则所有 triple 及更高项消失，而目标右端为零。因此点态可行性强制

$$
A(u,v)\le0
\qquad(u+v\le1).
$$

特别地，任何统一的

$$
c_{pq}=\lambda z_pz_q,\qquad \lambda>0,
$$

都不可能满足 fractional (F)：取 \(z_p=z_q=1/2\) 即得反例。

因此 0/1 证明中的正 pair coefficient 不能直接替换为正的 \(z_pz_q\) coefficient。正系数只能从总权重已经越过 \(1\) 的高阶 support 开始。

---

## Lemma 13 `[PROVED]`：固定阶 pointwise polynomial 不可能

固定次数 \(d\)。考虑相等权重

$$
u_i=\varepsilon,
\qquad
\varepsilon d\le1.
$$

若一个关于活跃坐标个数 \(q\) 的次数不超过 \(d\) 的多项式 \(P(q)\) 满足

$$
(\varepsilon q-C)^+
\le P(q)
\le
(\varepsilon q-1)^+
\tag{9.1}
$$

对所有足够大的整数 \(q\) 成立，则矛盾。

因为在

$$
q=0,1,\ldots,d
$$

上两侧 hinge 都为零，故

$$
P(0)=P(1)=\cdots=P(d)=0.
$$

次数不超过 \(d\) 的多项式有 \(d+1\) 个根，只能恒等于零；但当 \(q>C/\varepsilon\) 时左端为正。

这严格说明：

$$
\boxed{
\text{任意小权重要求交互阶数随 }1/\varepsilon\text{ 墑长。}
}
$$

pair–triple 或任何固定有限阶 ansatz 不能通过一个 pointwise sandwich 解决完整 fractional 情形。它若要工作，必须依赖 aggregate moment cancellation，而不是局部多项式本身。

---

# 十、random-partition certificate：捕获好，但误差带符号

## Lemma 14 `[PROVED]`：partition sandwich

把所有 prime-power atoms 任意分配到 \(r\) 个颜色类。令 \(S_c(n)\) 为第 \(c\) 类的总贡献。则逐点有

$$
(S(n)-r)^+
\le
\sum_{c=1}^r(S_c(n)-1)^+
\le
(S(n)-1)^+.
\tag{10.1}
$$

### 证明

上界由

$$
(a-1)^++(b-1)^+\le(a+b-1)^+
$$

反复使用得到。

另一方面，

$$
\sum_c(S_c-1)^+
=
S-\sum_c\min(S_c,1)
\ge S-r,
$$

且左侧非负。∎

若将每个 atom 独立均匀分配到 \(r\) 个颜色，并对分配取期望，定义

$$
F_r(n)
:=
\mathbb E_\chi
\sum_{c=1}^r(S_c(n)-1)^+,
$$

则

$$
(S(n)-r)^+
\le F_r(n)\le(S(n)-1)^+.
\tag{10.2}
$$

这是一个完整的 pointwise fractional sandwich。

### Möbius 系数

在 squarefree 模型中，设 \(a_A\) 是

$$
Q\longmapsto (z(Q)-1)^+
$$

的 Boolean Möbius 系数。则 \(F_r\) 的系数为

$$
a_A^{(r)}=r^{1-|A|}a_A.
\tag{10.3}
$$

原因是一个给定 atom 集全部进入同一个指定颜色的概率为 \(r^{-|A|}\)，而颜色共有 \(r\) 个。

---

## Lemma 15 `[PROVED]`：random-partition 的负支撑误差不能被忽略

取 \(N\) 个相等权重 \(z_i=1/2\)。函数

$$
f(q)=\left(\frac q2-1\right)^+
$$

的 Newton/Möbius 系数为

$$
a_j
=
\frac12(-1)^{j-3}(j-2)
\qquad(j\ge3).
\tag{10.4}
$$

特别地，

$$
a_3=\frac12,\qquad a_4=-1.
$$

经 \(r\)-color averaging 后，每个四元组的系数为

$$
-\frac1{r^3}.
$$

因此，在 \(N\) 个不同素数上，尚未聚合的负支撑质量至少为

$$
\frac1{r^3}\binom N4,
\tag{10.5}
$$

随 \(N\) 无界增长。

所以不能仅凭 (10.2) 得到 counting certificate：P3 的负系数 \(+1\) 成本会吞掉结论。必须利用：

* 这些四元组乘积是否超过 \(m\)；
* 不同负项是否具有相同 lcm；
* 或者使用一个没有负系数的重新编码。

---

# 十一、负系数 \(+1\) 成本是 sharp 的

## Lemma 16 `[PROVED]`：Boolean-cube adversary move

取一个不同素数组成的集合 \(A\)，并假设

$$
d_A:=\prod_{p\in A}p\le m.
$$

从标准多重集 \(K=\{1,\ldots,m\}\) 出发，定义一个有符号修改：

$$
\delta_A
:=
\sum_{Q\subseteq A}
(-1)^{|A|-|Q|}\delta_{d_Q},
\qquad
d_Q:=\prod_{p\in Q}p.
\tag{11.1}
$$

所有带负号的 \(d_Q\) 都是 \(K\) 中真实存在的一行，因此可以删除一份；带正号的行增加一份。修改后的多重集仍非负，且总质量不变，因为

$$
\sum_{Q\subseteq A}(-1)^{|A|-|Q|}=0.
$$

对任意模数 \(d_B\)，

$$
\sum_{Q\supseteq B}(-1)^{|A|-|Q|}
=
\begin{cases}
1,&B=A,\\
0,&B\ne A.
\end{cases}
$$

因此所有 divisor counts 不变，唯独

$$
N(d_A)
$$

增加 1。它仍位于

$$
\left[
\left\lfloor\frac m{d_A}\right\rfloor,
\left\lfloor\frac m{d_A}\right\rfloor+1
\right].
$$

所以这是一个完全合法的 A3 adversary move。

若 \(f(Q)\) 是任意依赖于所选素数支撑的成本函数，则成本变化恰为其 Möbius 系数

$$
\Delta_Af(\varnothing)
=
\sum_{Q\subseteq A}
(-1)^{|A|-|Q|}f(Q).
\tag{11.2}
$$

负 Möbius coefficient 因而可以被 abstract adversary 精确兑现。

---

## 显式小实例

取

$$
A=\{2,3,5,7\},\qquad m=210,
\qquad z_2=z_3=z_5=z_7=\frac12.
$$

增加一份：

$$
1,\ 6,\ 10,\ 14,\ 15,\ 21,\ 35,\ 210;
$$

删除一份：

$$
2,\ 3,\ 5,\ 7,\ 30,\ 42,\ 70,\ 105.
$$

总共各 8 份。所有 \(N(d)\) 不变，唯独

$$
N(210):1\longmapsto2.
$$

所以两侧 interval count bounds 全部满足。

成本变化为：

* 新增的六个 pair products 权重为 \(1\)，成本 0；
* 新增 \(210\) 权重为 \(2\)，成本 1；
* 删除的四个 singleton 成本 0；
* 删除的四个 triple products 权重为 \(3/2\)，每个成本 \(1/2\)。

净变化

$$
1-4\cdot\frac12=-1.
$$

这说明负系数的额外一个单位绝不是 P3 估计过粗产生的人为损失；抽象对手确实能够逐个利用它。

该实例不反驳任何 absolute-\(C\) hinge，因为此处 \(S(k)\le2\)。它反驳的是“忽略负系数误差也没关系”这一中间主张。

---

# 十二、sliding-window certificate：无负误差，但有碎片障碍

## Lemma 17 `[PROVED]`：显式非负 fractional certificate

把全部有限原子 \(a\) 排成某个固定顺序。原子 \(a\) 的长度为 \(\alpha_a\)，依次组成区间分割

$$
[0,Z),\qquad
Z=\sum_a\alpha_a.
$$

对

$$
0\le t\le Z-1,
$$

令 \(A_t\) 为与单位窗口 \([t,t+1]\) 相交的原子集合。

定义

$$
c_A
:=
\operatorname{Leb}\{t:A_t=A\}\ge0.
\tag{12.1}
$$

若一个整数 \(n\) 的活跃原子集合为 \(Q(n)\)，则

$$
\sum_{A\subseteq Q(n)}c_A
=
\operatorname{Leb}\{
t:[t,t+1]\subseteq
\bigcup_{a\in Q(n)}J_a
\}.
\tag{12.2}
$$

活跃 blocks 在固定顺序中分成若干 runs，设各 run 的总长度为

$$
\ell_1,\ldots,\ell_r.
$$

则

$$
F_\sigma(n)
:=
\sum_{A\subseteq Q(n)}c_A
=
\sum_{i=1}^r(\ell_i-1)^+.
\tag{12.3}
$$

因此

$$
F_\sigma(n)
\le
\left(\sum_i\ell_i-1\right)^+
=
(S(n)-1)^+.
\tag{12.4}
$$

把同一 \(A\) 的原子模数取 lcm，并将相同 lcm 的系数合并，即得到一个真正的 divisor certificate。所有系数均非负，所以没有任何 \(+1\) 负误差，而且

$$
V(c)=\sum_{k\le m}F_\sigma(k).
\tag{12.5}
$$

因此，只要能找到一个顺序或顺序的凸组合，使

$$
\sum_{k\le m}F_\sigma(k)
\ge
\sum_{k\le m}(S(k)-C)^+,
\tag{12.6}
$$

就完成了 fractional \((\mathrm{TH}_C)\)。

---

## Lemma 18 `[PROVED]`：单个顺序不可能 pointwise 给出绝对常数

取 \(2r\) 个权重均为 1 的素数原子。无论怎样排序，选择排序中每隔一个原子组成集合 \(Q\)。它有 \(r\) 个互不相邻的 runs，每个 run 长度为 1。因此

$$
F_\sigma(Q)=0,
$$

但

$$
S(Q)=r.
$$

令 \(m\) 至少为这些素数之积，则对应整数确实位于 \([1,m]\)。

所以单一 ordering 不可能逐点满足

$$
F_\sigma(Q)\ge(S(Q)-C)^+
$$

对某个绝对 \(C\) 成立。

这没有排除 aggregate ordering 或若干 orderings 的凸组合，但说明 sliding-window 路线也需要真正的全局算术结构。

---

# 十三、两类证书的精确互补

目前得到的结构可以概括为：

### random partition

$$
(S-r)^+\le F_r\le(S-1)^+.
$$

优点：pointwise 捕获完整，高负载时斜率为 1。

缺点：Möbius 系数带符号；负支撑质量可达

$$
\binom N4/r^3
$$

甚至更大，而 Lemma 16 证明 abstract adversary 能真实利用这些负项。

### sliding window

$$
0\le F_\sigma\le(S-1)^+.
$$

优点：全部系数非负，interval transfer 无损。

缺点：只捕获连续活跃 runs；任意一个顺序都有无界 fragmentation。

因此剩余证明不能只是从二者中任选一个。需要一种层次化结构，使：

1. 在高 \(S(k)\) 的 \(K\)-patterns 上，能够共享同一个 deductible 1，而不是每个尺度、每个 block 各付一次；
2. 所有负修正都落在 product \(\le m\) 的模数上，或被同一层的 capped-mass slack 精确支付；
3. 对任意巨大 interval integer \(b\)，证书仍保持 pointwise (F)，不能只对 \(k\le m\) 有效。

这正是“hierarchical anchors”需要满足的数学内容。

---

# 十四、最小的后续目标

random-partition certificate 给出一个非常具体的 sufficient condition。

设 \(\gamma_d^{(r)}\) 是 \(F_r\) 聚合到 lcm 后的 divisor coefficients，并定义

$$
\mathcal E_r
:=
\sum_{\gamma_d^{(r)}<0}
|\gamma_d^{(r)}|.
\tag{14.1}
$$

则

$$
V(\gamma^{(r)})
=
\sum_{k\le m}F_r(k)-\mathcal E_r.
\tag{14.2}
$$

由于

$$
F_r(k)\ge(S(k)-r)^+,
$$

若能证明

$$
\boxed{
\mathcal E_r
\le
\sum_{k\le m}
\min\bigl((S(k)-r)^+,\,r\bigr),
}
\tag{RP\(_r\)}
$$

则

$$
V(\gamma^{(r)})
\ge
\sum_{k\le m}(S(k)-2r)^+.
$$

于是 \((\mathrm{TH}_{2r})\) 成立。

对于当前 sparse core，可以先攻击 \(r=64\)。若 \((\mathrm{RP}_{64})\) 成立，则：

* 小模数部分得到阈值 \(128\)；
* 大模数 peel 再损失 1；

从而完整 fractional \((\mathrm{TH}_{129})\) 成立，并推出

$$
g(n)\le145n.
$$

Lemma 15–16 表明 \((\mathrm{RP}_r)\) 不能由抽象 coefficient counting 直接得到；必须使用 \(d_A\le m\)、floor multiplicities 和 lcm aggregation。

---

# 十五、有限检查方案

建议下一轮的 exact LP / adversary 检查只搜索已经压缩后的 sparse core：

$$
m>4096,\qquad
p^j\le m/64,\qquad
H_{64}<17/16.
$$

## Primal abstract adversary

变量是有限 valuation patterns \(t\) 的质量 \(y_t\ge0\)，约束：

$$
\sum_ty_t=m,
$$

$$
\left\lfloor\frac md\right\rfloor
\le
\sum_{t:d\mid t}y_t
\le
\left\lfloor\frac md\right\rfloor+1
\qquad(d\le m).
$$

目标：

$$
\min\sum_ty_t(S(t)-1)^+.
$$

与

$$
W_C=\sum_{k\le m}(S(k)-C)^+
$$

比较。

需要显式加入 Lemma 16 的 cube moves，作为 constraint-generation 的 adversarial seeds；否则 LP 很容易错过负 Möbius directions。

## Dual certificate search

候选支持至少应包括：

* baseline \(c_1,c_{p^j}\)；
* random-partition \(F_r\) 聚合后的 lcm；
* unit-window chains；
* Boolean-cube move 暴露出的负方向；
* product 接近 \(m\) 的 minimal overweight supports。

所有计算使用有理数。输出必须包含：

* primal pattern masses；
* 全部 active divisor constraints；
* dual \(c_d\)；
* exact primal/dual equality；
* 独立 checker，而不是复用求解器内部浮点值。

本轮有限代数检查脚本：

[下载 fractional follow-up 2 exact checker](sandbox:/mnt/data/erdos708_fractional_followup2_verify.py)

它精确检查：

* 9 坐标 vertex-to-cube 反例；
* dyadic、pair 和 independent-rounding 小反例；
* triangle dependent-rounding 障碍；
* \(R=64\) dense 常数；
* sliding-window coefficient 的非负性和 run 公式；
* random-partition 四阶负系数；
* bounded-degree root obstruction。

---

# 十六、Lean 形式化需求

dense theorem 不需要解析数论。

1. 用有限 `Finset` 表示原子 \((p,j)\)，权重为非负实数或有理数。
2. 证明 telescope identity：

   $$
   \min(zv,1)=\sum_j\alpha_j1_{j\le v}.
   $$
3. 证明大模数 peel：
   不同素数的两个模数均大于 \(m/64\) 时，其积大于 \(m\)。
4. 形式化

   $$
   \lfloor x\rfloor\ge\frac{63}{64}x
   \quad(x\ge64).
   $$
5. 二阶矩展开；不同素数时 lcm 为乘积。
6. 标量不等式

   $$
   \min(t,64)\ge t-\frac{t^2}{256},
   $$

   可由分段后 `nlinarith` 完成。
7. 有限贪心选择 \(Q\)，使用每项 \(h_p\le1/2\)。
8. counting certificate transfer。
9. Boolean-cube adversary move使用有限 Boolean lattice Möbius inversion。
10. sliding-window certificate 可以避免完整测度论：所有变化点来自有限集合

    $$
    a_i,\quad a_i-1,
    $$

    在相邻有理端点区间上 \(A_t\) 恒定。

---

# 最终依赖图

$$
\boxed{
H_{64}\ge\frac{17}{16}
\Longrightarrow
(\mathrm{TH}_{65})
\;\leftarrow\;
\text{Lemmas 1--5}
\;\leftarrow\;
\text{无未证明项}.
}
$$

$$
\boxed{
\text{完整 }(\mathrm{TH}_{65})
\;\leftarrow\;
\text{Theorem 6}
+
(\mathrm{SC}_{64})
\;\leftarrow\;
(\mathrm{SC}_{64})\text{ 未证明}.
}
$$

$$
\boxed{
\text{正 dyadic fractionalization 不可能}
\;\leftarrow\;
\text{Lemma 8}
\;\leftarrow\;
u=(1/2,1/2).
}
$$

$$
\boxed{
\text{0/1 cube 黑箱延拓不可能}
\;\leftarrow\;
\text{Lemma 9}
\;\leftarrow\;
7\text{ 个 9-全集 vs. }36\text{ 个 pairs}.
}
$$

$$
\boxed{
\text{固定阶 pair--triple 不可能 pointwise 闭合}
\;\leftarrow\;
\text{Lemmas 12--13}
\;\leftarrow\;
\text{任意小相等权重}.
}
$$

$$
\boxed{
\text{random partition 路线}
\;\leftarrow\;
(\mathrm{RP}_r)
\;\leftarrow\;
\text{尚缺利用 product/lcm 的负误差支付定理}.
}
$$

$$
\boxed{
\text{sliding-window 路线}
\;\leftarrow\;
\text{aggregate bounded-fragmentation ordering}
\;\leftarrow\;
\text{尚缺层次化 ordering/anchor 构造}.
}
$$

最后，进度消息中提到的 rough-number 障碍只排除了固定父映射

$$
k\mapsto k/P^+(k)
$$

所生成的 matching 子图；它没有排除“允许删除任意一个素因子层”的完整 matching graph。本答案没有使用该未经证明的 matching 主张。
