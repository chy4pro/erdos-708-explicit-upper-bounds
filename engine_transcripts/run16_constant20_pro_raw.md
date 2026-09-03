# 结论

**[PROVED — T2]** 令所有对数均为自然对数。对任意有限支撑权重 \(0\le z_p\le1\)、任意整数 \(m\ge3\)、任意 \(x\ge0\)，都有

$$
\boxed{\;
\sum_{k=1}^{m}\bigl(w(k)-20\log\log m\bigr)^+
\le
\sum_{b=x+1}^{x+m}\bigl(w(b)-1\bigr)^+
\;}
\tag{TH\(_{20\log\log m}\)}
$$

其中 \(w(n)=\sum_p z_pv_p(n)\)。

对 \(m=1,2\)，取 \(c=2\) 即可。因此可统一写成

$$
c(m)=
\begin{cases}
2,&m\le2,\\
20\log\log m,&m\ge3.
\end{cases}
$$

这严格完成 **T2，常数 \(C=20\)**。最终证明没有未证猜想。

核心改进不是继续优化原来的二进制分层，而是：

1. 把层比从 \(2\) 改为

   $$
   q=\frac{51}{50};
   $$
2. 允许 gain 参数 \(G\) 等于全部几何层数 \(Q\)，而不再要求 \(G\le2H\)；
3. 对每层使用满足精确阶乘条件的 \(\rho(k)\)，而不是统一的粗略 \(16H+\cdots\)。

细分层使原来每个二进制层都支付的 \(O(H)\) 预算，变成总共只支付约一次 \(eH\)。

---

# 1. 素数倒数质量

## Lemma 1 — **[PROVED]**

设 \(L>1\)，令

$$
h_L:=\log(1+\log L),\qquad H_L:=e\,h_L.
$$

若 \(\mathcal D\) 是一族两两互素且不小于 \(2\) 的整数，则

$$
\sum_{\substack{d\in\mathcal D\\d\le L}}\frac1d\le H_L.
\tag{1.1}
$$

### 证明

对每个 \(d\in\mathcal D\) 选一个素因子 \(p(d)\mid d\)。两两互素性保证这些 \(p(d)\) 两两不同，并且

$$
\frac1d\le\frac1{p(d)}.
$$

因此只需证明

$$
\sum_{p\le L}\frac1p\le e\log(1+\log L).
$$

取

$$
s=1+\frac1{\log L}>1.
$$

当 \(p\le L\) 时，

$$
p^{s-1}=p^{1/\log L}\le e,
$$

故

$$
\sum_{p\le L}\frac1p
\le e\sum_p\frac1{p^s}
\le e\log\zeta(s).
$$

又有

$$
\zeta(s)
=\sum_{n\ge1}n^{-s}
\le1+\int_1^\infty t^{-s}\,dt
=1+\frac1{s-1}
=1+\log L.
$$

代入即得 (1.1)。∎

---

# 2. 带双边区间误差的随机稀释下界

设 \(J\) 是任意一个长度为 \(L\) 的正整数区间，

$$
\nu_{\mathcal D}(n):=\#\{d\in\mathcal D:d\mid n\}.
$$

记

$$
R:=\lfloor\log_2L\rfloor.
$$

## Lemma 2 — **[PROVED]**

设 \(1\le k\le R-1\)，并令

$$
y:=L^{1/(k+1)},\qquad
\mathcal D_0:=\{d\in\mathcal D:d\le y\}.
$$

设

$$
e_r:=\sum_{\substack{S\subseteq\mathcal D_0\\ |S|=r}}
\frac1{\prod_{d\in S}d},
\qquad
H\ge\sum_{d\in\mathcal D_0}\frac1d,
\qquad H\ge1.
$$

则

$$
\boxed{\;
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}
\ge
\frac{L e_k}{4(8H)^k}.
\;}
\tag{2.1}
$$

### 证明

以概率

$$
\tau:=\frac1{8H}
$$

独立保留 \(\mathcal D_0\) 中的每个模数，得到随机子族 \(\mathcal D'\)。令

$$
r(n):=\nu_{\mathcal D'}(n).
$$

对每个整数 \(r\ge0\)，有二项 Bonferroni 不等式

$$
\mathbf 1_{r\ge k}
\ge
\binom rk-k\binom r{k+1}.
\tag{2.2}
$$

事实上：

* \(r<k\) 时两边均为 \(0\)；
* \(r=k,k+1\) 时右边等于 \(1\)；
* \(r\ge k+2\) 时右边不大于 \(0\)。

区间中 \(d\) 的倍数个数满足

$$
\frac Ld-1
\le N_J(d)
\le \frac Ld+1.
\tag{2.3}
$$

设 \(M=|\mathcal D_0|\)。对 (2.2) 求和、再对随机稀释取期望：

$$
\begin{aligned}
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}
&\ge
\mathbb E\sum_{n\in J}
\left[
\binom{r(n)}k-k\binom{r(n)}{k+1}
\right]\\
&\ge
\tau^k\left(Le_k-\binom Mk\right)
-k\tau^{k+1}
\left(Le_{k+1}+\binom M{k+1}\right).
\end{aligned}
\tag{2.4}
$$

现在估计三个误差项。

首先，由 \(k\le R-1\) 得 \(L\ge2^{k+1}\)，故 \(y\ge2\)。每个 \(k\)-元子集的乘积不超过 \(y^k\le L/2\)，从而

$$
\binom Mk\le y^k e_k\le\frac L2e_k.
\tag{2.5}
$$

每个 \((k+1)\)-元子集的乘积不超过 \(y^{k+1}=L\)，故

$$
\binom M{k+1}\le Le_{k+1}.
\tag{2.6}
$$

最后，

$$
(k+1)e_{k+1}
\le
\left(\sum_{d\in\mathcal D_0}\frac1d\right)e_k
\le He_k.
\tag{2.7}
$$

所以

$$
2k\tau Le_{k+1}
\le
\frac{2k}{k+1}\tau H\,Le_k
\le\frac14Le_k.
$$

将 (2.5)–(2.7) 代回 (2.4)：

$$
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}
\ge
\tau^k\left(1-\frac12-\frac14\right)Le_k
=
\frac{Le_k}{4(8H)^k}.
$$

∎

这个证明同时使用了 (2.3) 的上下两侧，因而没有假设区间中的模数事件彼此独立或近似独立。

---

# 3. 上尾与任意 gain

## Lemma 3 — **[PROVED]**

在 Lemma 2 的条件下，对任意整数 \(\rho\ge0\)，

$$
\#\{n\le L:\nu_{\mathcal D}(n)\ge2k+\rho\}
\le
\frac{Le_kH^\rho}{\rho!}.
\tag{3.1}
$$

### 证明

一个 \(n\le L\) 不可能被 \(k+1\) 个大于 \(y\) 的两两互素模数同时整除，因为它们的乘积严格大于

$$
y^{k+1}=L.
$$

所以，若 \(\nu_{\mathcal D}(n)\ge2k+\rho\)，那么至少有 \(k+\rho\) 个来自 \(\mathcal D_0\) 的模数整除 \(n\)。联合界给出

$$
\#\{n\le L:\nu_{\mathcal D}(n)\ge2k+\rho\}
\le Le_{k+\rho}.
$$

而

$$
e_{k+\rho}\le e_ke_\rho
\le e_k\frac{H^\rho}{\rho!}.
$$

因此得到 (3.1)。∎

---

## Lemma 4 — **[PROVED：任意 \(G\)]**

给定 \(G\ge1\)，定义

$$
A=A(H,G,k):=\log(4G)+k\log(8H),
\qquad h_0:=eH,
$$

以及

$$
s(A):=
\min\left\{
A,\,
\frac{2A}{\log(2+A/h_0)}
\right\},
$$

$$
\rho(H,G,k):=\left\lceil h_0+s(A)\right\rceil.
\tag{4.1}
$$

则

$$
\boxed{\;
G\cdot
\#\{n\le L:\nu_{\mathcal D}(n)\ge2k+\rho(H,G,k)\}
\le
\#\{n\in J:\nu_{\mathcal D}(n)\ge k\}.
\;}
\tag{4.2}
$$

这里 **\(G\) 没有 \(G\le2H\) 的限制**。

### 证明

由 Lemma 2、3，只需证明

$$
\rho!\ge4G(8H)^kH^\rho.
\tag{4.3}
$$

利用

$$
\rho!\ge\left(\frac{\rho}{e}\right)^\rho,
$$

充分条件为

$$
\rho\log\frac{\rho}{eH}\ge A.
\tag{4.4}
$$

下面证明 (4.1) 保证 (4.4)。

令 \(u=A/h_0\)。

第一候选 \(h_0+A=h_0(1+u)\) 满足

$$
h_0(1+u)\log(1+u)\ge h_0u=A,
$$

因为 \((1+u)\log(1+u)\ge u\)。

对第二候选，令

$$
v:=\frac{2u}{\log(2+u)}.
$$

要证

$$
(1+v)\log(1+v)\ge u.
\tag{4.5}
$$

若 \(\log(2+u)\le2\)，则 \(v\ge u\)，故 (4.5) 立即成立。

若 \(\log(2+u)\ge2\)，置 \(y=2+u\ge e^2\)。此时

$$
v=\frac{2(y-2)}{\log y}.
$$

函数

$$
\frac{2(y-2)}{\sqrt y\log y}
$$

在 \(y\ge e^2\) 上递增，因为其对数导数乘以 \(y\) 为

$$
\frac{y}{y-2}-\frac12-\frac1{\log y}
\ge
\frac{y}{y-2}-1>0.
$$

在 \(y=e^2\) 时该函数已大于 \(1\)，故 \(v\ge\sqrt y\)。于是

$$
\log(1+v)\ge\log v\ge\frac12\log y,
$$

从而

$$
(1+v)\log(1+v)
\ge
v\frac12\log y
=u.
$$

因此两个候选都满足 (4.4)，其较小者也满足。取上整不影响不等式。结合 Lemma 2、3 即得 (4.2)。∎

---

# 4. 细几何层编码

固定

$$
q:=\frac{51}{50},\qquad \delta:=q-1=\frac1{50}.
$$

设

$$
X(n):=\sum_p\min(u_pv_p(n),1),
\qquad 0<u_p\le1,
$$

其中只有有限多个 \(u_p\ne0\)。

令

$$
R=\lfloor\log_2L\rfloor,
$$

并定义

$$
k_j:=\lceil q^j\rceil.
$$

令 \(Q\) 是满足 \(k_j\le R-1\) 的非负整数 \(j\) 的个数。因此层为

$$
j=0,\dots,Q-1.
$$

对每层定义两两互素模数族

$$
\mathcal D_j:=
\left\{
p^{\,\lceil q^{-j}/u_p\rceil}:u_p>0
\right\},
$$

以及

$$
N_j(n):=\nu_{\mathcal D_j}(n).
$$

由定义，

$$
\min(u_pv_p(n),1)\ge q^{-j}
\iff
p^{\,\lceil q^{-j}/u_p\rceil}\mid n.
\tag{4.6}
$$

令

$$
\alpha_j:=\delta q^{-j}.
$$

## Lemma 5 — **[PROVED]**

对任意 \(n\le L\)，

$$
X(n)\le
\sum_{j=0}^{Q-1}\alpha_jN_j(n)
+
R q^{1-Q}.
\tag{5.1}
$$

并且

$$
N_j(n)\ge k_j\quad\Longrightarrow\quad X(n)\ge1.
\tag{5.2}
$$

### 证明

对单个 \(a\in(0,1]\)，设 \(j_0\) 是第一个满足 \(q^{-j_0}\le a\) 的整数。则

$$
\sum_{j\ge0}\delta q^{-j}\mathbf 1_{a\ge q^{-j}}
=
\sum_{j\ge j_0}\delta q^{-j}
=q^{1-j_0}\ge a.
$$

从第 \(Q\) 层开始的尾和为

$$
\sum_{j\ge Q}\delta q^{-j}=q^{1-Q}.
$$

而 \(n\le L\) 最多有 \(R\) 个不同素因子，因此求和得到 (5.1)。

若 \(N_j(n)\ge k_j\)，则至少有 \(k_j\) 个素数贡献不小于 \(q^{-j}\)，故

$$
X(n)\ge k_jq^{-j}\ge1.
$$

∎

---

# 5. 加权事件比较

对每个 \(j\) 令

$$
\rho_j:=\rho(H_L,Q,k_j)
$$

为 Lemma 4 中的整数，并定义

$$
B_L:=
\sum_{j=0}^{Q-1}
\alpha_j(2k_j+\rho_j).
\tag{5.3}
$$

## Lemma 6 — **[PROVED]**

设 \(h_L\ge4\)。对任意长度为 \(L\) 的正整数区间 \(J\)，

$$
\#\{n\le L:X(n)\ge B_L+2\}
\le
\#\{n\in J:X(n)\ge1\}.
\tag{6.1}
$$

### 证明

由 \(k_Q=\lceil q^Q\rceil>R-1\) 得

$$
q^Q>R-2.
$$

由于 \(h_L\ge4\) 时 \(R\ge77\)，

$$
Rq^{1-Q}
<
\frac{qR}{R-2}
<2.
\tag{6.2}
$$

假设 \(X(n)\ge B_L+2\)。若对全部 \(j\) 都有

$$
N_j(n)\le2k_j+\rho_j-1,
$$

则由 (5.1) 和 (6.2)，

$$
\begin{aligned}
X(n)
&<
\sum_{j<Q}\alpha_j(2k_j+\rho_j-1)+2\\
&=
B_L-\sum_{j<Q}\alpha_j+2
<B_L+2,
\end{aligned}
$$

矛盾。因此某一层满足

$$
N_j(n)\ge2k_j+\rho_j.
$$

对每层应用 Lemma 4，取 \(G=Q\)：

$$
Q\#\{n\le L:N_j(n)\ge2k_j+\rho_j\}
\le
\#\{n\in J:N_j(n)\ge k_j\}.
$$

对 \(j\) 求和，并使用 (5.2)：

$$
\begin{aligned}
\#\{n\le L:X(n)\ge B_L+2\}
&\le
\frac1Q\sum_{j<Q}
\#\{n\in J:N_j(n)\ge k_j\}\\
&\le
\#\{n\in J:X(n)\ge1\}.
\end{aligned}
$$

∎

---

# 6. 显式常数预算

## Lemma 7 — **[PROVED；唯一有限区间证书]**

若 \(h=h_L\ge4\)，则

$$
\boxed{\;
B_L+3<19.24\,h.
\;}
\tag{7.1}
$$

从而

$$
\boxed{\;
\#\{n\le L:X(n)\ge19.25h_L-1\}
\le
\#\{n\in J:X(n)\ge1\}.
\;}
\tag{7.2}
$$

### 证明

写

$$
H=eh,\qquad h_0=eH=e^2h,\qquad
\ell:=\log(8H)=\log(8eh).
$$

---

## 6.1 层数

由

$$
Q\le1+\frac{\log R}{\log q},
\qquad
R<\frac{e^h}{\log2},
$$

以及

$$
-\log\log2<0.367,\qquad
\log(1.02)>0.0198,
$$

可得，对 \(h\ge4\)，

$$
Q<56h.
\tag{7.3}
$$

此外

$$
\sum_{j<Q}\alpha_j<q=1.02.
\tag{7.4}
$$

由 \(k_j\le q^j+1\)，

$$
2\sum_{j<Q}\alpha_jk_j
\le
2\delta Q+2q
<
2.24h+2.04.
\tag{7.5}
$$

---

## 6.2 \(\rho_j\) 的基线部分

设

$$
A_j=\log(4Q)+k_j\ell.
$$

由 \(\rho_j\le h_0+s(A_j)+1\)，

$$
\sum_{j<Q}\alpha_j(h_0+1)
<
q(e^2h+1)
<
7.538h+1.02.
\tag{7.6}
$$

---

## 6.3 \(s(A_j)\) 的子可加性

令

$$
f(t):=
\min\left\{
t,\frac{2t}{\log(2+t/h_0)}
\right\}.
$$

因为 \(f(t)/t\) 单调不增，故

$$
f(a+b)\le f(a)+f(b).
$$

因此

$$
s(A_j)
\le
\log(4Q)
+
k_j\ell\,g(k_j),
\tag{7.7}
$$

其中

$$
g(u):=
\min\left\{
1,\frac2{\log(2+\beta u)}
\right\},
\qquad
\beta:=\frac{\ell}{e^2h}.
$$

第一项满足

$$
q\log(4Q)
<
1.02\log(224h)
<
1.734h,
\tag{7.8}
$$

因为 \(\log(224h)/h\) 在 \(h\ge4\) 上递减。

对于第二项，由 \(g\) 递减、\(k_j\le q^j+1\)，

$$
\begin{aligned}
\sum_{j<Q}\alpha_jk_jg(k_j)
&\le
q+\delta\sum_{j<Q}g(q^j)\\
&\le
q+\delta+
\frac{\delta}{\log q}
\int_1^R g(u)\,\frac{du}{u}.
\end{aligned}
\tag{7.9}
$$

并且

$$
\frac{\delta}{\log q}<1.01.
\tag{7.10}
$$

---

## 6.4 积分

记

$$
v_0:=e^2-2.
$$

若 \(\beta R\le v_0\)，则积分直接不超过 \(\log R\)。若 \(\beta R>v_0\)，在 \(v_0/\beta\) 处分段，并用

$$
\log(2+v)\ge\log v
$$

得到

$$
\int_1^R g(u)\frac{du}{u}
\le
\log\frac{v_0}{\beta}
+
2\log\frac{\log(\beta R)}{\log v_0}.
\tag{7.11}
$$

另外

$$
\log(\beta R)
<
h-\log h+\log\ell-2-\log\log2
\le h-\frac32.
\tag{7.12}
$$

最后一步使用了：

* \(\ell/h\) 在 \(h\ge4\) 上递减；
* 在 \(h=4\) 时

  $$
  \log(\ell/h)<0.111
  <
  \frac12+\log\log2.
  $$

故在两种情形下统一有

$$
\int_1^R g(u)\frac{du}{u}
\le J(h),
\tag{7.13}
$$

其中

$$
J(h):=
\log\frac{v_0e^2h}{\ell}
+
2\log\frac{h-\frac32}{\log v_0}.
\tag{7.14}
$$

所需的一元数值不等式是

$$
\boxed{\;
\frac{\ell J(h)}h<5
\qquad(h\ge4).
\;}
\tag{7.15}
$$

对于 \(h\ge8\)，它可以纯解析验证：

$$
J(h)<3\log h+1.01,\qquad
\ell<\log h+3.08.
$$

令 \(y=\log h\)。函数

$$
(y+3.08)(3y+1.01)e^{-y}
$$

在 \(y\ge\log8\) 上递减，并且在 \(y=\log8\) 处小于

$$
\frac{5.16\cdot7.25}{8}=4.67625<5.
$$

区间 \(4\le h\le8\) 被分成 \(80\) 个长度 \(1/20\) 的有理区间。由于 \(\ell\) 和 \(J\) 均递增，在 \([a,b]\) 上

$$
\frac{\ell(h)J(h)}h
\le
\frac{\ell(b)J(b)}a.
$$

80 位有向区间算术给出的最大上界为

$$
4.965229461230080<5,
$$

出现在区间 \([4.40,4.45]\)。

因此由 (7.9)、(7.10)、(7.15)，

$$
\ell\sum_{j<Q}\alpha_jk_jg(k_j)
<
6.212h.
\tag{7.16}
$$

---

## 6.5 汇总

由 (7.5)、(7.6)、(7.8)、(7.16)，

$$
B_L
<
(7.538+2.240+1.734+6.212)h
+(1.02+2.04).
$$

再加上编码尾部小于 \(2\) 和最终 hinge 的 \(1\)，总常数项不超过

$$
1.02+2.04+3=6.06\le1.515h
\qquad(h\ge4).
$$

所以

$$
B_L+3
<
(7.538+2.240+1.734+6.212+1.515)h
=
19.239h
<
19.24h.
$$

这证明 (7.1)，继而由 Lemma 6 得到 (7.2)。∎

有限常数证书：

* [r9_constant_check.py](sandbox:/mnt/data/r9_constant_check.py)
* SHA-256：
  `cc4d6ee31bce3a97565ea17232e9ee497264146cb965009d3f39aa0d4a809756`

运行输出：

```text
bins=80
max_bin=[4.40,4.45]
max_upper=4.965229461230080
tail_at_8_upper=4.676250000000000
bookkeeping_coefficient=19.239000000000000
```

---

# 7. 排序恒等式

## Lemma 8 — **[PROVED]**

设 \(0\le r_i\le1\)，令

$$
R=\sum_i r_i,\qquad R_{<i}=\sum_{j<i}r_j.
$$

则对任意 \(T\ge0\)，

$$
\boxed{\;
(R-T-1)^+
\le
\sum_i r_i\mathbf1_{R_{<i}\ge T}
\le
(R-T)^+.
\;}
\tag{8.1}
$$

### 证明

被排除的初始段总质量不小于 \(T\)，但由于最后一个跨越 \(T\) 的增量至多为 \(1\)，不超过 \(T+1\)。剩余尾部质量因而夹在 \(R-T-1\) 与 \(R-T\) 之间。若从未跨越 \(T\)，中间和为 \(0\)，同样满足 (8.1)。∎

---

# 8. 商区间转移

固定素数的任意全序。定义

$$
a_p(n):=z_pv_p(n),
$$

$$
r_p(n):=\min(a_p(n),1),
\qquad
R(n):=\sum_pr_p(n),
$$

$$
E(n):=\sum_p(a_p(n)-1)^+.
$$

于是逐点有

$$
w(n)=E(n)+R(n).
\tag{8.2}
$$

而且

$$
(w(n)-1)^+
=
E(n)+(R(n)-1)^+.
\tag{8.3}
$$

确实，若 \(E(n)>0\)，则某个 \(r_p(n)=1\)，故 \(R(n)\ge1\)；若 \(E(n)=0\)，则 \(w(n)=R(n)\)。

---

## Lemma 9 — **[PROVED]**

设 \(m\) 满足

$$
h_m:=\log(1+\log m)\ge4,
\qquad
g_m:=\log\log m,
$$

并令

$$
T:=20g_m-1.
$$

则

$$
\sum_{k\le m}(R(k)-T-1)^+
\le
\sum_{b\in I}(R(b)-1)^+.
\tag{9.1}
$$

### 证明

由 Lemma 8，

$$
(R(k)-T-1)^+
\le
\sum_p r_p(k)\mathbf1_{R_{<p}(k)\ge T}.
\tag{9.2}
$$

将 \(r_p\) 按素数幂展开：

$$
r_p(n)
=
\sum_{j\ge1}\alpha_{p,j}\mathbf1_{p^j\mid n},
\tag{9.3}
$$

其中

$$
\alpha_{p,j}
=
\min(jz_p,1)-\min((j-1)z_p,1)\ge0.
$$

固定 \(d=p^j\)，令

$$
L_d:=\left\lfloor\frac md\right\rfloor.
$$

则

$$
\sum_{\substack{k\le m\\d\mid k}}
\mathbf1_{R_{<p}(k)\ge T}
=
\#\{\ell\le L_d:R_{<p}(\ell)\ge T\},
\tag{9.4}
$$

因为对于排在 \(p\) 之前的素数 \(q\ne p\)，

$$
v_q(d\ell)=v_q(\ell).
$$

区间 \(I\) 中 \(d\) 的倍数写成 \(d\ell\) 后，\(\ell\) 构成长度为 \(L_d\) 或 \(L_d+1\) 的连续区间。选择其中任意长度为 \(L_d\) 的子区间 \(J_d\)。

现在比较阈值。由

$$
g_m
=h_m+\log(1-e^{-h_m})
\ge0.995h_m
\qquad(h_m\ge4),
\tag{9.5}
$$

可得

$$
T\ge19.9h_m-1.
\tag{9.6}
$$

若 \(h_{L_d}\ge4\)，则

$$
T\ge19.9h_m-1
\ge19.25h_{L_d}-1,
$$

故由 Lemma 7，

$$
\#\{\ell\le L_d:R_{<p}(\ell)\ge T\}
\le
\#\{\ell\in J_d:R_{<p}(\ell)\ge1\}.
\tag{9.7}
$$

若 \(h_{L_d}<4\)，则

$$
R_{<p}(\ell)
\le\omega(\ell)
\le\log_2L_d
<
\frac{e^4-1}{\log2}
<77.4,
$$

而由 \(h_m\ge4\)，

$$
T>20\log(e^4-1)-1>78.6.
$$

所以左边为空，(9.7) 仍成立。

乘以 \(\alpha_{p,j}\)，对 \(p,j\) 求和：

$$
\sum_{k\le m}(R(k)-T-1)^+
\le
\sum_{b\in I}\sum_p
r_p(b)\mathbf1_{R_{<p}(b)\ge1}.
$$

再用 Lemma 8 的上界部分，阈值取 \(1\)：

$$
\sum_p
r_p(b)\mathbf1_{R_{<p}(b)\ge1}
\le
(R(b)-1)^+.
$$

于是得到 (9.1)。∎

---

# 9. 高素数幂的剥离

## Lemma 10 — **[PROVED]**

对任意长度为 \(m\) 的区间 \(I\)，

$$
\sum_{k\le m}E(k)\le\sum_{b\in I}E(b).
\tag{10.1}
$$

### 证明

逐素数有展开

$$
(a_p(n)-1)^+
=
\sum_{j\ge1}\beta_{p,j}\mathbf1_{p^j\mid n},
$$

其中

$$
\beta_{p,j}
=
(jz_p-1)^+-((j-1)z_p-1)^+
\ge0.
$$

而长度为 \(m\) 的任意区间中 \(p^j\) 的倍数不少于

$$
\left\lfloor\frac m{p^j}\right\rfloor,
$$

这正是 \([1,m]\) 中的倍数个数。对所有 \(p,j\) 以非负系数求和即可。∎

---

# 10. 大 \(m\) 情形的 hinge 结论

当 \(h_m\ge4\) 时，由 Lemma 9、10，

$$
\begin{aligned}
\sum_{k\le m}(w(k)-20g_m)^+
&=
\sum_{k\le m}(E(k)+R(k)-20g_m)^+\\
&\le
\sum_{k\le m}E(k)
+
\sum_{k\le m}(R(k)-20g_m)^+\\
&=
\sum_{k\le m}E(k)
+
\sum_{k\le m}(R(k)-T-1)^+\\
&\le
\sum_{b\in I}E(b)
+
\sum_{b\in I}(R(b)-1)^+\\
&=
\sum_{b\in I}(w(b)-1)^+.
\end{aligned}
$$

这证明了所有满足 \(h_m\ge4\) 的 \(m\)。

---

# 11. 小 \(m\) 情形

## Lemma 11 — **[PROVED]**

若 \(m\ge4\) 且

$$
\log(1+\log m)<4,
$$

则

$$
\max_{k\le m}w(k)
\le20\log\log m.
\tag{11.1}
$$

因而左边 hinge 恒为零。

### 证明

令 \(t=\log m\)。此时

$$
\log4\le t<e^4-1.
$$

函数

$$
f(t)=\frac t{\log t}
$$

在 \((1,e)\) 上递减、在 \((e,\infty)\) 上递增。因此该区间上的最大值出现在端点。直接的有向区间估计给出

$$
f(\log4)<4.245,
$$

$$
f(e^4-1)<13.462,
$$

而

$$
20\log2>13.862.
$$

因此

$$
\frac{\log m}{\log2}
\le20\log\log m.
$$

另一方面

$$
w(k)\le\sum_pv_p(k)=\Omega(k)\le\log_2k\le\log_2m.
$$

故得到 (11.1)。∎

当 \(m=3\) 时，

$$
20\log\log3=1.880956\ldots>1,
$$

而 \(w(1)=0,\ w(2),w(3)\le1\)，故左边也是 \(0\)。

当 \(m=1,2\) 时，取 \(c=2\)，左边显然为 \(0\)。

至此定理对所有 \(m\) 成立。

---

# 对抗审计

## A. 密集窗口 — **[COMPUTED；非证明依赖]**

没有使用低 \(m\) 的 \(TH_{20\log\log m}\) 直接测试，因为在可计算范围内该阈值通常超过 \(\max w(k)\)，这种检查接近空检查。

实际测试的是非平凡的 Lemma 2：

* 模数族：

  * 前 12 个素数；
  * \(2,9,25,49,121,169,289,361,529,841\)；
  * \(4,9,25,49,121,169,289,361\)；
* \(L\in\{64,128,256,512,1024\}\)；
* \(k=1,2,3\) 中所有非零下界配置；
* 每个配置穷举 \(x=0,\dots,4999\)。

共 \(23\) 个配置、\(115000\) 个窗口。最小的

$$
\frac{\text{实际最小计数}}{\text{Lemma 2 下界}}
$$

为 \(10.5\)，对应

$$
\mathcal D=(4,9,25,49,121,169,289,361),\quad
L=64,\quad k=1,\quad x=175.
$$

## B. 抽象 valuation multiset — **[COMPUTED；非证明依赖]**

建立整数 LP：

* 变量 \(n_S\) 表示恰具有模数模式 \(S\) 的元素个数；
* 对每个非空 \(A\) 强制

  $$
  \left\lfloor\frac L{\prod_{d\in A}d}\right\rfloor
  \le
  \sum_{S\supseteq A}n_S
  \le
  \left\lfloor\frac L{\prod_{d\in A}d}\right\rfloor+1;
  $$
* 最小化 \(\sum_{|S|\ge k}n_S\)。

测试了 5 个非平凡配置。最接近 Lemma 2 下界的配置为

$$
L=50000,\quad
\mathcal D=(4,9,25,49),\quad
k=1,
$$

其中 LP 最优值为 \(18646\)，Lemma 2 下界为 \(1562.5\)，比值

$$
11.93344.
$$

## C. 许多轻权重

此处不依赖数值实验。几何编码尾部是

$$
Rq^{1-Q},
$$

只依赖 \(n\le L\) 的不同素因子个数不超过 \(R\)，与权重多小无关。

## D. 高素数幂

完全由 Lemma 10 的非负素数幂增量剥离，未用截断近似。

可重跑的完整审计：

* [r9_adversarial_check.py](sandbox:/mnt/data/r9_adversarial_check.py)
* [运行输出](sandbox:/mnt/data/r9_adversarial_check.txt)

SHA-256：

```text
deba2c8ca79a6cea850131287bd4ad109327b7a4e8846265fac7617a68c193bc  r9_adversarial_check.py
77d6aaada6a2c42f97ca3cafd19e42f8204616c75d17cf08bc61282ee4f05688  r9_adversarial_check.txt
```

---

# Lean 形式化需要的组件

1. **区间倍数计数**

   $$
   L/d-1\le N_J(d)\le L/d+1.
   $$

2. **有限随机稀释**
   在有限 powerset 概率空间中形式化期望；不需要测度论的无限版本。

3. **Bonferroni 多项式**

   $$
   \mathbf1_{r\ge k}\ge\binom rk-k\binom r{k+1}.
   $$

4. **初等对称函数**

   $$
   (k+1)e_{k+1}\le He_k,\qquad
   e_{k+\rho}\le e_kH^\rho/\rho!.
   $$

5. **素数倒数界**
   通过 \(s=1+1/\log L\)、有限 Euler 乘积和积分上界形式化。

6. **阶乘反演**

   $$
   n!\ge(n/e)^n
   $$

   以及 Lemma 4 中的一元不等式。

7. **常数证书**
   唯一需要有限实数区间验证的是

   $$
   \ell J(h)/h<5,\quad 4\le h\le8.
   $$

   可用 80 个有理区间和 `Real.log` 的有理上下界替换 `mpmath.iv`。

8. **几何层编码**
   需要处理 `ceil`、有限初始段 \(Q\) 和尾和 \(q^{1-Q}\)。

9. **排序恒等式与素数幂展开**
   都是有限和与 telescope。

---

# 依赖表

$$
\boxed{
\text{T2：}(TH_{20\log\log m})
}
$$

依赖于

$$
\text{Lemma 8--10：排序、商区间、幂剥离}
$$

依赖于

$$
\text{Lemma 6--7：加权事件比较及 }19.24h\text{ 预算}
$$

依赖于

$$
\text{Lemma 4--5：任意 gain 的阶乘反演及 }51/50\text{ 几何编码}
$$

依赖于

$$
\text{Lemma 1--3：素数倒数、双边 Bonferroni、上尾联合界}.
$$

**未证项目：无。**

---

# 与 T1 的精确差距

本证明没有得到绝对常数。残留的 \(\log\log L\) 来自 Lemma 4：

$$
\rho\log\frac{\rho}{eH}\ge A.
$$

即使 \(k\) 固定、层比 \(q\downarrow1\)，仍需

$$
\rho\gtrsim eH,
\qquad
H=e\log(1+\log L).
$$

细几何层把原来“每个二进制层支付一次 \(H\)”改成“所有层总共支付约一次 \(eH\)”，从而把常数降到 \(20\)；但要完成 T1，必须进一步把这个 \(k=1\) 附近的 \(eH\) 基线替换为真正的**典型层分布比较**，而不能继续依赖

$$
e_{k+\rho}\le e_kH^\rho/\rho!
$$

这一上尾联合界。
