# 结论

本轮得到三个严格结论。

1. **T1 的 0/1 版本成立，而且可取绝对常数 \(C=4\)**：

$$
\boxed{\;
\sum_{k\le m}\bigl(\Omega_P(k)-4\bigr)^+
\le
\sum_{b=x+1}^{x+m}\bigl(\Omega_P(b)-1\bigr)^+
\;}
\tag{TH\(_4^{0/1}\)}
$$

对任意 \(m\ge1\)、\(x\ge0\) 和任意有限素数集 \(P\) 都成立，其中

$$
\Omega_P(n):=\sum_{p\in P}v_p(n).
$$

证明完全由显式 counting certificates 给出，不使用 CRT 误差相关性、筛法 thinning 或 \(\log\log m\) 分层。

2. **T2 按其当前表述不可能成立。** 对 \(P=\{p:p\le m\}\)，任何满足抽象区间计数下界的对手，其代价已经至少为 \(\sum_{k\le m}(\Omega(k)-2)^+\)。因此，更不可能低于阈值 \(c(m)\to\infty\) 的左端。

3. 对 P3 中的**平坦锚点族**，T3 有一个显式反例：

$$
Y=2^{41},\qquad m=(8Y)^4=2^{176},\qquad
P=\{p\text{ prime}:Y<p\le8Y\}.
$$

任意锚点集 \(R\subseteq P\) 都不能在阈值 \(3\) 证明所需不等式；即使给它附加所有正的素数幂系数也失败。不过，同一个 \(P\) 可被非锚点的 pair–triple certificate 在阈值 \(2\) 解决。因此失败的是平坦锚点表示，而不是 counting 本身。

唯一剩余的实质缺口是：把 \(C=4\) 从 0/1 权重推广到任意 \(z_p\in[0,1]\)。

---

# 一、Counting transfer

## 引理 1 `[PROVED]`：证书传递

设只有有限多个 \(c_d\ne0\)，且对所有 \(n\ge1\),

$$
\sum_{d\mid n}c_d\le (w(n)-1)^+.
\tag{F}
$$

令

$$
V_m(c):=
\sum_{c_d>0}c_d\left\lfloor\frac md\right\rfloor
-
\sum_{c_d<0}|c_d|
\left(\left\lfloor\frac md\right\rfloor+1\right).
$$

则对任意长度为 \(m\) 的整数区间 \(I\),

$$
\sum_{b\in I}(w(b)-1)^+\ge V_m(c).
$$

### 证明

令

$$
N_I(d):=\#\{b\in I:d\mid b\}.
$$

总有

$$
\left\lfloor\frac md\right\rfloor
\le N_I(d)\le
\left\lfloor\frac md\right\rfloor+1.
$$

于是

$$
\begin{aligned}
\sum_{b\in I}(w(b)-1)^+
&\ge
\sum_{b\in I}\sum_{d\mid b}c_d\\
&=\sum_dc_dN_I(d)\\
&\ge V_m(c).
\end{aligned}
$$

这里正系数使用下界，负系数使用上界。∎

同样的证明对 A3 中的抽象 valuation-pattern multiset 或总质量为 \(m\) 的测度成立。

---

# 二、把重复素因子和大素数剥离

以下固定有限素数集 \(P\)，并写

$$
\Omega_P(n)=\sum_{p\in P}v_p(n),\qquad
\omega_P(n)=\#\{p\in P:p\mid n\}.
$$

定义重复指数部分

$$
e_P(n):=\Omega_P(n)-\omega_P(n)
       =\sum_{p\in P}(v_p(n)-1)^+.
$$

令

$$
y:=\lfloor m^{1/3}\rfloor,\qquad
S:=\{p\in P:p\le y\},\qquad
L:=P\setminus S.
$$

并定义

$$
A:=\sum_{\substack{p\in P\\j\ge2,\ p^j\le m}}
\left\lfloor\frac m{p^j}\right\rfloor.
$$

## 引理 2 `[PROVED]`：立方根剥离

有

$$
A=\sum_{k\le m}e_P(k),
\tag{2.1}
$$

且每个 \(k\le m\) 至多被两个 \(L\)-中的不同素数整除。因此

$$
(\Omega_P(k)-4)^+
\le e_P(k)+(\omega_S(k)-2)^+,
\tag{2.2}
$$

从而

$$
\sum_{k\le m}(\Omega_P(k)-4)^+
\le
A+\sum_{k\le m}(\omega_S(k)-2)^+.
\tag{2.3}
$$

### 证明

恒等式 (2.1) 来自

$$
(v_p(k)-1)^+=\sum_{\substack{j\ge2\\p^j\le m}}1_{p^j\mid k}
\qquad(k\le m).
$$

若三个不同的 \(L\)-素数整除 \(k\)，则

$$
k\ge(y+1)^3>m,
$$

矛盾。因此 \(\omega_L(k)\le2\)。

再用一般不等式

$$
(a+b-C)^+\le a+(b-C)^+
\qquad(a\ge0)
$$

得到

$$
\begin{aligned}
(\Omega_P(k)-4)^+
&=(e_P(k)+\omega_P(k)-4)^+\\
&\le e_P(k)+(\omega_P(k)-4)^+\\
&\le e_P(k)+(\omega_S(k)-2)^+.
\end{aligned}
$$

求和即得。∎

---

# 三、稀疏支：pair–triple certificate

定义小素数的调和质量

$$
H:=\sum_{p\in S}\frac1p,
\qquad
\eta:=\left(1+\frac1y\right)H.
$$

本支处理

$$
\eta\le2.
\tag{S}
$$

## 引理 3 `[PROVED]`：显式稀疏证书满足 (F)

定义证书：

$$
c_{p^j}=1
\quad
(p\in P,\ j\ge2,\ p^j\le m),
\tag{3.1}
$$

$$
c_{pq}=\frac{11}{21}
\quad(p,q\in S,\ p<q),
\tag{3.2}
$$

$$
c_{pqr}=-\frac17
\quad(p,q,r\in S,\ p<q<r),
\tag{3.3}
$$

其他 \(c_d=0\)。

则对所有 \(n\ge1\),

$$
\sum_{d\mid n}c_d\le(\Omega_P(n)-1)^+.
$$

### 证明

记

$$
r:=\omega_S(n),\qquad t:=\omega_P(n).
$$

pair–triple 部分恰为

$$
\begin{aligned}
\phi(r)
&=\frac{11}{21}\binom r2-\frac17\binom r3\\
&=\frac{r(r-1)(13-r)}{42}.
\end{aligned}
$$

对整数 \(r\ge1\),

$$
r(13-r)\le42,
$$

因为整数上的最大值在 \(r=6,7\) 取得，且等于 \(42\)。故

$$
\phi(r)\le r-1.
$$

当 \(r=0\) 时 \(\phi(r)=0\)。因此总有

$$
\phi(r)\le(r-1)^+\le(t-1)^+.
$$

素数幂部分不超过 \(e_P(n)\)。若 \(t\ge1\)，则

$$
e_P(n)+(t-1)=\Omega_P(n)-1.
$$

若 \(t=0\)，证书和为 \(0\)。故 (F) 成立。∎

---

## 引理 4 `[PROVED]`：稀疏支的证书值覆盖阈值 \(4\)

定义

$$
E_j:=
\sum_{\substack{B\subseteq S\\|B|=j}}
\left\lfloor\frac m{\prod_{p\in B}p}\right\rfloor
=
\sum_{k\le m}\binom{\omega_S(k)}j,
\qquad j=2,3,
$$

以及

$$
M_3:=\binom{|S|}{3}.
$$

在条件 \(\eta\le2\) 下，上述证书满足

$$
V_m(c)\ge
\sum_{k\le m}(\Omega_P(k)-4)^+.
$$

### 证明

首先，每个 \(S\)-三元组的乘积至多 \(y^3\le m\)，所以

$$
M_3\le E_3.
\tag{4.1}
$$

其次，

$$
\begin{aligned}
3E_3
&=
\sum_{\{p,q\}\subseteq S}
\sum_{r\in S\setminus\{p,q\}}
\left\lfloor\frac m{pqr}\right\rfloor\\
&\le
H\sum_{\{p,q\}\subseteq S}\frac m{pq}.
\end{aligned}
$$

对每个 \(p,q\in S\)，有 \(pq\le y^2\) 和

$$
\left\lfloor\frac m{pq}\right\rfloor\ge y.
$$

因此

$$
\frac m{pq}
<
\left\lfloor\frac m{pq}\right\rfloor+1
\le
\left(1+\frac1y\right)
\left\lfloor\frac m{pq}\right\rfloor.
$$

故

$$
3E_3\le\eta E_2\le2E_2,
\qquad
E_3\le\frac23E_2.
\tag{4.2}
$$

证书值为

$$
V_m(c)
=
A+\frac{11}{21}E_2-\frac17(E_3+M_3).
$$

利用 (4.1)–(4.2),

$$
\begin{aligned}
V_m(c)
&\ge
A+\frac{11}{21}E_2-\frac27E_3\\
&\ge
A+
\left(
\frac{11}{21}-\frac27\cdot\frac23
\right)E_2\\
&=
A+\frac13E_2.
\tag{4.3}
\end{aligned}
$$

另一方面，对所有整数 \(r\ge0\),

$$
(r-2)^+\le\frac13\binom r2.
\tag{4.4}
$$

对于 \(r\ge3\)，两边之差为

$$
\frac13\binom r2-(r-2)
=
\frac{(r-3)(r-4)}6\ge0;
$$

其余情形显然。

因此

$$
\sum_{k\le m}(\omega_S(k)-2)^+
\le\frac13E_2.
$$

结合引理 2 和 (4.3),

$$
V_m(c)\ge
A+\sum_{k\le m}(\omega_S(k)-2)^+
\ge
\sum_{k\le m}(\Omega_P(k)-4)^+.
$$

∎

系数 \(\frac{11}{21},-\frac17\) 并非任意选择。若使用对称 ansatz

$$
a\binom r2-b\binom r3\le r-1
$$

并要求在 \(E_3\le\eta E_2/3\) 下覆盖 \(E_2/3\)，则 \(r=6\) 的点态约束给出

$$
3a-1\le4b,
$$

所以这种二三阶 ansatz 至多能到 \(\eta=2\)。当前系数恰好在 \(r=6,7\) 取等，并达到 \(\eta=2\)。

---

# 四、稠密支：全素数幂基线

现在处理

$$
\eta>2.
\tag{D}
$$

## 引理 5 `[PROVED]`：稠密支证书

定义

$$
c_1=-1,
\qquad
c_{p^j}=1
\quad(p\in P,\ j\ge1,\ p^j\le m),
\tag{5.1}
$$

其他系数为零。则该证书满足 (F)，而且

$$
V_m(c)\ge
\sum_{k\le m}(\Omega_P(k)-4)^+.
$$

### 证明：点态可行性

对任意 \(n\)，证书的除数和为

$$
-1+
\sum_{\substack{p\in P,\ j\ge1\\p^j\le m\\p^j\mid n}}1.
$$

若 \(\Omega_P(n)=0\)，左边为 \(-1\le0\)。否则，正项之和至多为 \(\Omega_P(n)\)，故

$$
\sum_{d\mid n}c_d\le\Omega_P(n)-1
=(\Omega_P(n)-1)^+.
$$

### 证明：证书值

记

$$
B:=\sum_{k\le m}\Omega_P(k)
=
\sum_{\substack{p\in P,\ j\ge1\\p^j\le m}}
\left\lfloor\frac m{p^j}\right\rfloor.
$$

由定义，

$$
V_m(c)=B-(m+1).
\tag{5.2}
$$

因此只需证明

$$
\sum_{k\le m}\min(\Omega_P(k),4)\ge m+1.
\tag{5.3}
$$

### 构造一个调和质量介于 \(3/2\) 和 \(2\) 的子集

条件 \(\eta>2\) 不可能发生于 \(y\le4\)：此时直接检查

$$
\eta\le
0,\ \frac34,\ \frac{10}{9},\ \frac{25}{24}.
$$

故 \(y\ge5\)，并且

$$
H>\frac{2y}{y+1}\ge\frac53>\frac32.
$$

按任意固定顺序逐个加入 \(S\) 中的素数，直到倒数和第一次达到 \(3/2\)。得到 \(Q\subseteq S\)，满足

$$
\frac32\le H_Q:=\sum_{p\in Q}\frac1p<2,
\tag{5.4}
$$

因为最后加入的项至多为 \(1/2\)。此外

$$
|Q|\le y.
\tag{5.5}
$$

### 截断一阶矩

对任意整数 \(r\ge0\),

$$
\min(r,4)\ge r-\frac17\binom r2.
\tag{5.6}
$$

对于 \(r\le4\) 显然；对于 \(r\ge5\),

$$
4-\left(r-\frac17\binom r2\right)
=
\frac{(r-7)(r-8)}{14}\ge0
$$

在整数上成立。

令

$$
E_1(Q)=\sum_{p\in Q}\left\lfloor\frac mp\right\rfloor,
\qquad
E_2(Q)=\sum_{\{p,q\}\subseteq Q}
\left\lfloor\frac m{pq}\right\rfloor.
$$

则

$$
\begin{aligned}
\sum_{k\le m}\min(\omega_Q(k),4)
&\ge E_1(Q)-\frac17E_2(Q)\\
&\ge mH_Q-|Q|
-\frac m7\sum_{\{p,q\}\subseteq Q}\frac1{pq}\\
&\ge
m\left(H_Q-\frac{H_Q^2}{14}\right)-|Q|.
\end{aligned}
$$

函数

$$
f(h)=h-\frac{h^2}{14}
$$

在 \([3/2,2]\) 上递增。因此由 (5.4)–(5.5),

$$
\sum_{k\le m}\min(\omega_Q(k),4)
\ge
\frac{75}{56}m-y.
$$

由于 \(m\ge y^3\) 且 \(y\ge5\),

$$
\frac{19}{56}m\ge y+1.
$$

故

$$
\sum_{k\le m}\min(\Omega_P(k),4)
\ge
\sum_{k\le m}\min(\omega_Q(k),4)
\ge m+1.
$$

这证明了 (5.3)。

最后，由

$$
\Omega-(\Omega-4)^+=\min(\Omega,4)
$$

和 (5.2),

$$
\begin{aligned}
V_m(c)
-\sum_{k\le m}(\Omega_P(k)-4)^+
&=
\sum_{k\le m}\min(\Omega_P(k),4)-(m+1)\\
&\ge0.
\end{aligned}
$$

∎

---

# 五、主定理

## 定理 6 `[PROVED]`：T1 的 0/1 版本，\(C=4\)

对任意有限素数集 \(P\)、任意 \(m\ge1\) 和 \(x\ge0\),

$$
\boxed{
\sum_{k=1}^m(\Omega_P(k)-4)^+
\le
\sum_{b=x+1}^{x+m}(\Omega_P(b)-1)^+
}.
$$

### 证明

计算

$$
\eta=
\left(1+\frac1{\lfloor m^{1/3}\rfloor}\right)
\sum_{\substack{p\in P\\p\le\lfloor m^{1/3}\rfloor}}\frac1p.
$$

若 \(\eta\le2\)，使用引理 3–4 的 pair–triple certificate。

若 \(\eta>2\)，使用引理 5 的基线 certificate。

两种情形都得到满足 (F) 且

$$
V_m(c)\ge
\sum_{k\le m}(\Omega_P(k)-4)^+
$$

的显式证书。由引理 1 得结论。∎

### 抽象对手推论

对任何满足 A3 两侧计数约束的抽象多重集或测度，

$$
\sum_t(\Omega_P(t)-1)^+
\ge
\sum_{k\le m}(\Omega_P(k)-4)^+.
$$

因此在 0/1 情形，abstract adversary 不可能击破任何 \(c\ge4\)。

这个证明“只付一次调和质量”：

* 小素数调和质量稀疏时，二阶收益压过三阶负误差；
* 调和质量稠密时，全素数幂基线本身已有超过 \(m+1\) 的 capped mass。

没有把不同素数尺度的预算相加，因而没有产生 \(\log\log m\)。

---

# 六、T2 被严格排除

## 引理 7 `[PROVED]`：全素数情形的抽象对手甚至不能击破 \(c=2\)

取

$$
P=\{p:p\le m\},
\qquad w=\Omega.
$$

设抽象多重集有 \(m\) 个 valuation patterns，并满足

$$
N(d)\ge\left\lfloor\frac md\right\rfloor
\qquad(d\le m).
$$

则

$$
\sum_t(\Omega(t)-1)^+
\ge
\sum_{k\le m}(\Omega(k)-2)^+.
\tag{6.1}
$$

### 证明

因为 \((u-1)^+\ge u-1\),

$$
\sum_t(\Omega(t)-1)^+
\ge
\sum_t\Omega(t)-m.
$$

又因为

$$
\sum_t\Omega(t)
=
\sum_p\sum_{j\ge1}N(p^j)
\ge
\sum_{p^j\le m}\left\lfloor\frac m{p^j}\right\rfloor
=
\sum_{k\le m}\Omega(k),
$$

故抽象对手代价至少为

$$
S_m-m,\qquad
S_m:=\sum_{k\le m}\Omega(k).
$$

另一方面，

$$
\sum_{k\le m}\min(\Omega(k),2)
=
\pi(m)+2\bigl(m-1-\pi(m)\bigr)
=
2m-2-\pi(m).
$$

因此

$$
\sum_{k\le m}(\Omega(k)-2)^+
=
S_m-(2m-2-\pi(m)).
$$

两者之差为

$$
(S_m-m)
-
\sum_{k\le m}(\Omega(k)-2)^+
=
m-2-\pi(m)\ge0
$$

对 \(m\ge4\) 成立；\(m\le3\) 时右端为零。∎

所以只要 \(c(m)\ge2\),

$$
\sum_{k\le m}(\Omega(k)-c(m))^+
\le
\sum_{k\le m}(\Omega(k)-2)^+
\le
\sum_t(\Omega(t)-1)^+.
$$

故 T2 所要求的

$$
\sum_t(\Omega(t)-1)^+
\le
\sum_{k\le m}(\Omega(k)-c(m))^+-1
$$

不可能发生。这个排除甚至只用了计数下界，没有使用上界。

作为对应的显式 dual certificate，当 \(m\ge6\) 时可取

$$
c_1=-1,\qquad c_{p^j}=1\quad(p^j\le m).
$$

其值为

$$
S_m-m-1
$$

并且

$$
S_m-m-1-
\sum_{k\le m}(\Omega(k)-2)^+
=
m-3-\pi(m)\ge0.
$$

---

# 七、平坦锚点族在阈值 \(3\) 的显式失败

这里“锚点证书”严格指 P3 给出的那一族：选择 \(R\subseteq P\)，对 \(A\subseteq R\) 和 \(q\in P\setminus R\) 使用交替系数。允许额外加入所有素数幂正系数 \(c_{p^j}=1\)。

## 引理 8 `[PROVED]`：平坦锚点证书的精确值

记

$$
r:=|P|,\qquad s:=|R|.
$$

令

$$
A_m(P):=
\sum_{\substack{p\in P\\j\ge2,\ p^j\le m}}
\left\lfloor\frac m{p^j}\right\rfloor,
$$

以及

$$
H_R:=
\sum_{k\le m}
(\omega_P(k)-1)^+
\,1_{\{\,R\cap\{p:p\mid k\}\ne\varnothing\,\}}.
$$

则增广后的锚点证书值恰为

$$
V_R=A_m(P)+H_R-E(s,r),
\tag{7.1}
$$

其中

$$
E(0,r)=0,
$$

而对 \(s\ge1\),

$$
E(s,r)=
\bigl(2^{s-1}-s\bigr)
+
(r-s)\bigl(2^{s-1}-1\bigr).
\tag{7.2}
$$

### 证明

设一个数被 \(a\) 个锚点素数和 \(q\) 个非锚点素数整除。P3 的交替和等于

$$
(a-1)^++q\,1_{\{a>0\}}.
$$

即：命中锚点时等于全部不同素因子数减一，否则为零。

负系数个数如下：

* 纯锚点项中，负系数对应奇数大小 \(A\subseteq R\)，且 \(|A|\ge3\)，共有

  $$
  2^{s-1}-s;
  $$
* 每个非锚点 \(q\) 的项中，负系数对应非空偶数大小 \(A\)，共有

  $$
  2^{s-1}-1.
  $$

每个负系数在 \(V\) 中比普通 floor 求和多付一个单位，因此得到 (7.1)–(7.2)。∎

---

## 引理 9 `[PROVED]`：所需的初等素数计数界

令

$$
Y=2^{41}.
$$

则对

$$
r=\pi(8Y)-\pi(Y)
$$

有

$$
\frac{Y}{12}<r<\frac{3Y}{4},
\tag{7.3}
$$

并且还有较强的

$$
r<\frac{29Y}{41}.
\tag{7.4}
$$

### 证明

记

$$
\vartheta(x)=\sum_{p\le x}\log p.
$$

对二的幂 \(x\)，由区间 \((n,2n]\) 中素数的乘积整除 \(\binom{2n}{n}\)，逐层相加得到

$$
\vartheta(x)<2x\log2.
$$

将素数分为 \(p\le\sqrt x\) 和 \(p>\sqrt x\)，得到

$$
\pi(x)<\sqrt x+\frac{4x\log2}{\log x}.
\tag{7.5}
$$

另一方面，

$$
\binom{x}{x/2}\ge\frac{2^x}{x+1}.
$$

Legendre 公式给出 \(\binom{x}{x/2}\) 中每个素数的完整 \(p\)-主部不超过 \(x\)，故

$$
\binom{x}{x/2}\le x^{\pi(x)}.
$$

因此

$$
\pi(x)>
\frac{x\log2-\log(x+1)}{\log x}
>
\frac{x}{\log_2x}-2.
\tag{7.6}
$$

应用于 \(Y=2^{41}\) 和 \(8Y=2^{44}\)：

$$
\pi(Y)<2^{21}+\frac{4Y}{41},
$$

$$
\pi(8Y)>\frac{2Y}{11}-2.
$$

故

$$
r>
\frac{38Y}{451}-2^{21}-2.
$$

而

$$
\frac{38}{451}-\frac1{12}
=
\frac5{5412},
$$

并且

$$
\frac{5Y}{5412}>2^{21}+2.
$$

于是 \(r>Y/12\)。

又由

$$
\pi(8Y)<2^{22}+\frac{8Y}{11}<\frac{3Y}{4}
$$

得到 \(r<3Y/4\)。

最后由

$$
\pi(Y)>\frac{Y}{41}-2
$$

和上述 \(\pi(8Y)\) 上界，

$$
r<
2^{22}+2+
\left(\frac8{11}-\frac1{41}\right)Y
=
2^{22}+2+\frac{317Y}{451}.
$$

由于

$$
\frac{29}{41}=\frac{319}{451},
\qquad
\frac{2Y}{451}>2^{22}+2,
$$

得到 (7.4)。∎

---

## 定理 10 `[PROVED]`：所有平坦锚点选择在 \(c=3\) 失败

取

$$
Y=2^{41},\qquad
m=(8Y)^4=2^{176},
$$

$$
P=\{p\text{ prime}:Y<p\le8Y\}.
$$

则对每个 \(R\subseteq P\)，P3 平坦锚点证书，即使增广所有素数幂正系数，也满足

$$
V_R<
\sum_{k\le m}(\Omega_P(k)-3)^+.
\tag{7.7}
$$

### 证明

记 \(r=|P|\)、\(s=|R|\)。

由于 \(Y^5>m\)，素数幂部分只有指数 \(2,3,4\)，因此

$$
A_m(P)
<
2r\frac m{Y^2}.
\tag{7.8}
$$

另外，对每个命中锚点且含 \(t\) 个 \(P\)-素因子的数，其 \(t-1\) 可被有序对“一个锚点素因子、另一个 \(P\)-素因子”覆盖。因此

$$
H_R
\le
\sum_{p\in R}
\sum_{\substack{q\in P\\q\ne p}}
\left\lfloor\frac m{pq}\right\rfloor
<
sr\frac m{Y^2}.
\tag{7.9}
$$

由 \(r<3Y/4\) 和 \(m/Y^2=4096Y^2\),

$$
A_m(P)+H_R
<
3072(s+2)Y^3.
\tag{7.10}
$$

另一方面，每个四元素子集 \(B\subseteq P\) 的乘积不超过

$$
(8Y)^4=m,
$$

且在该乘积处 \((\Omega_P-3)^+=1\)。所以

$$
W_3:=
\sum_{k\le m}(\Omega_P(k)-3)^+
\ge\binom r4.
$$

由于 \(r>Y/12\) 且 \(r\ge6\),

$$
\binom r4\ge\frac{r^4}{192}
>
\frac{Y^4}{192\cdot12^4}
=
\frac{Y^4}{3\,981\,312}.
\tag{7.11}
$$

### 情形 1：\(s\le177\)

由 (7.10),

$$
A_m(P)+H_R
<
179\cdot3072\,Y^3.
$$

而精确整数比较为

$$
179\cdot3072\cdot3\,981\,312
=
2\,189\,275\,693\,056
<
2^{41}=Y.
$$

故

$$
A_m(P)+H_R<W_3.
$$

再减去非负的 \(E(s,r)\)，得到 \(V_R<W_3\)。

### 情形 2：\(s\ge178\)

由 \(s\le r<3Y/4\),

$$
A_m(P)+H_R<3072Y^4.
$$

而

$$
E(s,r)\ge2^{s-1}-s\ge2^{s-2}\ge2^{176}.
$$

同时

$$
3072Y^4<4096Y^4=2^{176}.
$$

因此

$$
V_R=A_m(P)+H_R-E(s,r)<0<W_3.
$$

两种情形覆盖所有 \(R\subseteq P\)。∎

由于 \(V\) 对证书线性，任何对这些平坦锚点证书的随机选择或凸混合也同样失败。

---

## 引理 11 `[PROVED]`：同一个 \(P\) 被非锚点证书在 \(c=2\) 解决

上述 \(P,m\) 并不是 counting 的反例。使用

$$
c_{p^j}=1\quad(j\ge2),
\qquad
c_{pq}=\frac{11}{21},
\qquad
c_{pqr}=-\frac17
$$

即可证明

$$
V_m(c)\ge
\sum_{k\le m}(\Omega_P(k)-2)^+.
$$

### 证明

由引理 9，

$$
H_P:=\sum_{p\in P}\frac1p
<
\frac rY
<
\frac{29}{41}.
$$

任意 \(p,q\in P\) 满足

$$
\left\lfloor\frac m{pq}\right\rfloor
\ge64Y^2.
$$

因此同引理 4 的计算给出

$$
3E_3
\le
H_P\left(1+\frac1{64Y^2}\right)E_2
<E_2.
$$

证书值满足

$$
\begin{aligned}
V_m(c)
&\ge
A+\frac{11}{21}E_2-\frac27E_3\\
&>
A+
\left(\frac{33}{21}-\frac27\right)E_3\\
&=
A+\frac97E_3
\ge A+E_3.
\end{aligned}
$$

而

$$
(\Omega_P(k)-2)^+
\le e_P(k)+(\omega_P(k)-2)^+,
$$

并且

$$
(r-2)^+\le\binom r3.
$$

求和得到

$$
\sum_{k\le m}(\Omega_P(k)-2)^+
\le A+E_3.
$$

∎

所以 A2 的固定锚点损失确实存在，但“指数多个锚点子集的 \(+1\) 代价”不是 counting 的普遍障碍；低阶非锚点证书绕过了它。

---

# 八、为什么 0/1 定理不能直接平均成 fractional 定理

## 引理 12 `[PROVED]`：阈值 layer-cake 平均不保持 fractional 的 (F)

取两个素数 \(p,q\)，令

$$
z_p=z_q=\frac12.
$$

对 \(t\in[0,1]\)，设

$$
P_t=\{r:z_r\ge t\}.
$$

在 \(n=pq\) 处，

$$
w(n)=1,
\qquad
(w(n)-1)^+=0.
$$

但当 \(0<t\le1/2\) 时，

$$
\Omega_{P_t}(n)=2,
$$

所以

$$
\int_0^1(\Omega_{P_t}(n)-1)^+\,dt
=
\frac12>0.
$$

因此，把 0/1 certificates 按随机阈值或 layer-cake 求期望，得到的点态上界通常是

$$
w(n)-\max_{p\mid n}z_p,
$$

而不是

$$
(w(n)-1)^+.
$$

这精确说明了当前 0/1 证明与全 fractional T1 之间的缺口。

---

# 九、独立计算攻击

复核脚本包括：

* 对三个关键整数多项式逐点检查到 \(r=100000\)；
* 穷举所有 \(m\le43\) 以及 \(P\subseteq\{p:p\le m\}\)，共 \(68251\) 个实例；
* 300 个较大随机素数集，包括 \(p>m\)；
* 一个真实进入稠密支的参数：

  $$
  y=269,\quad m=269^3,\quad P=\{p:p\le269\};
  $$
* 对若干实例精确扫描所有 \(0\le x\le3000\) 的区间；
* 对 \(2\le m\le24\) 枚举所有截断 valuation patterns，并用 primal continuous LP 同时施加每个

  $$
  \lfloor m/d\rfloor\le N(d)\le\lfloor m/d\rfloor+1
  $$

  约束；
* 对平坦锚点公式进行随机小实例的直接系数展开检查；
* 对 T3 中的所有巨大整数常数作精确整数比较。

脚本运行输出：

```text
round-10 C=4 verification: all checks passed
```

SHA-256：

```text
96d4e53f19adba5cbf76b26197ef6bd4dc5a87768ce99a04f8d6f868efdef536
```

[复核脚本：erdos708_round10_c4_verify.py](sandbox:/mnt/data/erdos708_round10_c4_verify.py)

这些计算不参与主定理证明；主证明是引理 1–5 的有限代数推导。LP 是独立 primal 对手，而不是从证书反算的必然通过检查。

---

# 十、Lean 形式化所需组件

主定理的 Lean 化不需要解析数论或素数定理，只需要以下有限组合结构：

1. 用 `Finset Nat.Prime` 表示 \(P\)，用有限支撑 `Finsupp ℕ ℚ` 表示 \(c_d\)。
2. 形式化

   $$
   \Omega_P(n),\quad \omega_P(n),\quad e_P(n)
   $$

   及

   $$
   e_P(n)=\sum_{j\ge2}1_{p^j\mid n}.
   $$
3. 长度 \(m\) 区间中 \(d\)-倍数个数的 floor/ceil 引理。
4. 引理 1 的正负系数分拆。
5. 整数立方根 \(y\) 的性质

   $$
   y^3\le m<(y+1)^3.
   $$
6. 有限子集计数恒等式

   $$
   \sum_{\{p,q\}}1_{pq\mid n}=\binom{\omega_S(n)}2,
   \quad
   \sum_{\{p,q,r\}}1_{pqr\mid n}=\binom{\omega_S(n)}3.
   $$
7. 三个整数多项式引理：

   $$
   \frac{11}{21}\binom r2-\frac17\binom r3\le(r-1)^+,
   $$

   $$
   (r-2)^+\le\frac13\binom r2,
   $$

   $$
   \min(r,4)\ge r-\frac17\binom r2.
   $$

   都可分有限小情形后由 `ring_nf`、`nlinarith` 完成。
8. 稠密支的最短前缀 \(Q\)：每项不超过 \(1/2\)，总和大于 \(3/2\)，故存在前缀和位于 \([3/2,2)\)。
9. T3 若也形式化，还需：

   * 奇偶子集数量；
   * central binomial coefficient 的简单上下界；
   * Legendre 指数界；
   * 最后的固定大整数 `norm_num`。

---

# 最终依赖图

$$
\boxed{
\text{T1}_{0/1},\ C=4
\ \leftarrow\
\text{引理 1}
+
\text{引理 2}
+
\bigl[(\eta\le2):\text{引理 3--4}\bigr]
+
\bigl[(\eta>2):\text{引理 5}\bigr]
\ \leftarrow\
\text{无未证明项}
}
$$

$$
\boxed{
\text{T2 不可能}
\ \leftarrow\
\text{引理 7}
\ \leftarrow\
\text{无未证明项}
}
$$

$$
\boxed{
\text{P3 平坦锚点族在 }c=3\text{ 失败}
\ \leftarrow\
\text{引理 8--10}
\ \leftarrow\
\text{无未证明项}
}
$$

$$
\boxed{
\text{该失败不是 counting 障碍}
\ \leftarrow\
\text{引理 11}
\ \leftarrow\
\text{无未证明项}
}
$$

$$
\boxed{
\text{完整 T1（任意 }z_p\in[0,1]\text{）}
\ \leftarrow\
\text{尚缺 fractional 点态证书}
\ \leftarrow\
\text{朴素阈值平均被引理 12 排除}
}
$$
