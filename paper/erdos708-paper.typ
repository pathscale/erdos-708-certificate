#set page(
  paper: "us-letter",
  margin: (left: 0.95in, right: 0.95in, top: 0.9in, bottom: 0.9in),
  numbering: "1",
)
#set document(
  title: "Exact Small-n Values (g(4) = 5, g(5) = 6, g(6) = 8) and Constructive Lower Bounds (g(7) ≥ 9, g(8) ≥ 11) for Erdős Problem 708",
  author: "C. Bergström",
)

#set text(font: "Libertinus Serif", size: 10.3pt, hyphenate: false)
#set par(justify: true, leading: 0.62em, spacing: 0.8em)
#set heading(numbering: "1.")
#show heading: set block(above: 1.2em, below: 0.6em, sticky: true)
#show raw.where(block: false): it => text(size: 9.4pt, font: "DejaVu Sans Mono", it.text.replace("_", "_\u{200b}"))

#let pmod(m) = $space ("mod" #m)$
#let ZZ = $bb(Z)$
#let prod = math.product
#let lcm = math.op("lcm")
#let fs = math.op("fs")

#align(center)[
  #set par(justify: false)
  #text(size: 14pt, weight: "bold")[
    Exact Small-$n$ Values ($g(4) = 5$, $g(5) = 6$, $g(6) = 8$) and \
    Constructive Lower Bounds ($g(7) >= 9$, $g(8) >= 11$) for Erdős Problem 708
  ]
  #v(0.5em)
  #text(size: 11pt, weight: "semibold")[C. Bergström]
  #v(0.15em)
  #text(size: 9.8pt)[24x AI Research]
  #v(0.14em)
  #text(size: 9pt)[ORCID: `0009-0008-7153-1817`]
  #v(0.18em)
  #text(size: 9.5pt)[November 2026]
]

#v(0.65em)
#pad(x: 1.8em)[
  #text(weight: "bold")[Abstract.]
  For $n >= 1$, let $g(n)$ denote the smallest integer such that for every $n$-element subset $A subset.eq ZZ_(>= 2)$ with maximum $M = max(A)$ and every interval $I$ of $M$ consecutive positive integers, there exists a subset $B subset.eq I$ of cardinality $|B| <= g(n)$ satisfying $prod_(a in A) a divides prod_(b in B) b$. Erdős and Surányi (1959) proved $g(3) = 4$ and $g(n) >= (2 - o(1)) n$, and Erdős Problem 708 asks whether $g(n) <= (2 + o(1)) n$. We determine the exact values $g(4) = 5$, $g(5) = 6$, and $g(6) = 8$, and construct explicit Chinese Remainder Theorem witnesses establishing $g(7) >= 9$ and $g(8) >= 11$. Our upper-bound proofs combine sum-maximal divisor-closure and interval-splitting reductions, an unrestricted Universal Cumulative-GCD Slot Theorem (yielding the bipartite spanning-forest bound $tau(A, I) <= 2 n - r - s + 1$, achieved with equality on our $n = 8$ witness), universal prime-support elimination, and $g(d)$-subset tail decoupling. These structural reductions pair certified exhaustive verification below explicit finite cutoffs ($7 <= M <= 3","481$ for $n = 6$) with closed-form descending factor-packing bounds for all larger $M$. Unconditional asymptotic upper bounds derived from related peeling and linear-programming duality techniques are developed in the companion manuscript @bergstrom26asymptotic.
]

= Introduction, Prior Work, and Main Results

For a finite subset $A = {a_1 < a_2 < dots < a_n} subset.eq ZZ_(>= 2)$ with maximum element $M = a_n$ and an interval $I = {x + 1, x + 2, dots, x + M}$ of $M$ consecutive positive integers ($x in ZZ_(>= 0)$), define the minimum product-cover number
$ tau(A, I) := min { |B| : B subset.eq I, space prod_(a in A) a divides prod_(b in B) b }, $
and, following Erdős and Surányi @erdossuranyi59 and Bloom @bloom708, define the Erdős–Surányi function#footnote[Requiring $|B| <= g(n)$ rather than literal equality $|B| = g(n)$ is essential (as also observed by L. Mazur on the _Erdős Problems_ forum): taking $A = {2, dots, n + 1}$ on $I = {1, dots, n + 1}$ forces $|B| <= |I| = n + 1$, whereas $g(n) >= (2 - o(1)) n$.]
$ g(n) := sup { tau(A, I) : A subset.eq ZZ_(>= 2), space |A| = n, space I = {x + 1, dots, x + max(A)}, space x >= 0 }. $

This problem was posed in 1959 by Erdős and Surányi @erdossuranyi59 and highlighted by Erdős in his 1992 and 1995 problem papers @erdos92c @erdos95 for determining whether $g(n) <= (2 + o(1)) n$, or whether the strict inequality $g(n) <= 2 n$ holds for every $n >= 1$ (catalogued as Problem 708 in Bloom's _Erdős Problems_ database @bloom708).

*Prior work.* Gallai observed $g(2) = 2$ and $g(3) >= 4$, and Erdős and Surányi @erdossuranyi59 proved $g(3) = 4$ together with the asymptotic lower bound $g(n) >= (2 - o(1)) n$, achieved by taking $A = {p_i p_j : 1 <= i < j <= ell}$ for primes $p_1 < dots < p_ell$ satisfying $p_ell^2 < 2 p_1^2$ and centering a single multiple of $p_1 dots.c p_ell$ inside $I$. In September 2026, Chen @chen26 established the first unconditional upper bounds depending only on $n$, proving $g(n) <= 12 n$ (formalized end to end in Lean 4) and $g(n) <= 11 n$ via LP duality and weighted prime-factor hinge certificates, proving $tau(A, I) <= 2 n$ in the long-interval regime $M >= 8 n^3$, and recording computational lower bounds $g(4) >= 5$, $g(5) >= 6$, $g(10) >= 14$, and $g(12) >= 17$.

*Scope and main results.* The asymptotic conjecture $g(n) <= (2 + o(1)) n$ remains open in the intermediate interval regime $2 n < M < 8 n^3$ (for $M <= 2 n$, binomially $tau(A, I) <= M <= 2 n$). This paper establishes the exact values of $g(n)$ for $n in {4, 5, 6}$ via hybrid analytic and computer-assisted proofs (pairing certified finite verification below explicit cutoffs with analytic slot-packing reductions above), together with constructive lower bounds for $n in {7, 8}$:

*Theorem 1 (Exact small-$n$ values and constructive lower bounds).* The Erdős–Surányi function satisfies
$ g(1) = 1, quad g(2) = 2, quad g(3) = 4, quad g(4) = 5, quad g(5) = 6, quad g(6) = 8, $
together with the constructive lower bounds $g(7) >= 9$ and $g(8) >= 11$.

Notice that the successive differences $g(n) - g(n - 1)$ for $n = 2, dots, 6$ are $1, 2, 1, 1, 2$, and between $n = 6$ and $n = 8$ the function increases by at least $3$ ($g(8) - g(6) >= 11 - 8 = 3$). Table 1 summarizes the certified bounds and extremal witnesses for $1 <= n <= 8$.

#figure(
  table(
    columns: (auto, auto, 1.45fr, auto, 1fr),
    inset: (x: 5pt, y: 4pt),
    align: (center, center, left, right, left),
    stroke: 0.5pt,
    [*$n$*], [*Value / Bound*], [*Extremal Lower-Bound Witness $A_n$*], [*$M = max(A_n)$*], [*Reference / Status*],
    [$1$], [$g(1) = 1$], [$A_1 = {2}$ at $x = 0$ ($I = {1, 2}$)], [$2$], [Trivial],
    [$2$], [$g(2) = 2$], [$A_2 = {2, 3}$ at $x = 1$ ($I = {2, 3, 4}$)], [$3$], [Gallai @erdossuranyi59; Cor. 7],
    [$3$], [$g(3) = 4$], [$A_3 = {77, 91, 143}$ at $x = 631","559$], [$143$], [Erdős–Surányi @erdossuranyi59; Thm. 11],
    [$4$], [*$g(4) = 5$*], [$A_4 = {49, 77, 91, 143}$ at $x = 631","559$], [$143$], [*Exact theorem* (Prop. 2, Thm. 11)],
    [$5$], [*$g(5) = 6$*], [$A_5 = {289, 299, 323, 391, 437}$ at $x = 581","200","167$], [$437$], [*Exact theorem* (Prop. 3, Thm. 11)],
    [$6$], [*$g(6) = 8$*], [$A_6 = {221, 289, 299, 323, 391, 437}$ at $x = 581","200","167$], [$437$], [*Exact theorem* (Prop. 3, Thm. 12)],
    [$7$], [*$g(7) >= 9$*], [$A_7 = A_8 without {2419}$ at $x = x_8$], [$3","233$], [*Lower bound* (Prop. 4)],
    [$8$], [*$g(8) >= 11$*], [$A_8 = {41, 43, 47, 53} times {59, 61}$ at $x = x_8$], [$3","233$], [*Lower bound* (Prop. 4)],
  ),
  caption: [Exact values and constructive lower bounds for the Erdős–Surányi function $g(n)$, where $x_8 = 85","145","283","391","654","366","755$.],
)

= Constructive Lower Bounds for $3 <= n <= 8$

For a prime $p$ and integer $m >= 1$, write $v_p (m)$ for the $p$-adic valuation of $m$, write $A_p := {a in A : p divides a}$, and write $D_p (A) := sum_(a in A) v_p (a)$ for the total prime demand of $A$ at $p$. More generally, for any prime-demand vector $D = (D_p)_(p <= M)$ supported on $S subset.eq {p <= M}$, write
$ tau(D|_S, I) := min { |B| : B subset.eq I, space forall p in S, space sum_(b in B) v_p (b) >= D_p }. $
Then $prod_(a in A) a divides prod_(b in B) b$ holds if and only if $sum_(b in B) v_p (b) >= D_p (A)$ for every prime $p <= M$.

*Proposition 2 ($g(3) >= 4$ and $g(4) >= 5$).* Let $x_4 = 631","559$ and $I = {x_4 + 1, dots, x_4 + 143}$. Then $A_3 = {77, 91, 143} = {7 dot 11, 7 dot 13, 11 dot 13}$ satisfies $tau(A_3, I) = 4$, and $A_4 = {49, 77, 91, 143}$ satisfies $tau(A_4, I) = 5$.

_Proof._ The active primes are $(7, 11, 13)$, with demand $(2, 2, 2)$ on $A_3$ and $(4, 2, 2)$ on $A_4$. Note that $x_4 + 72 = 631","631 = 7 dot 11 dot 13 dot 631$, so the center offset $j = 72$ has valuation vector $(v_7, v_11, v_13) = (1, 1, 1)$. For every $j in {1, dots, 143} without {72}$, $|j - 72| <= 71 < 7 dot 11 = 77$, so $x_4 + j$ is divisible by at most one prime in ${7, 11, 13}$. Moreover, $x_4 + 2 = 631","561 equiv 0 pmod(49)$ ($j in {2, 51, 100}$ have $v_7 = 2$; $7^3 = 343$ divides none of them), $x_4 + 61 = 631","620 equiv 0 pmod(121)$ ($j = 61$ has $v_11 = 2$), and $x_4 + 72 equiv 6 dot 13 pmod(169)$, so no multiple of $13^2 = 169$ lies in $I$ ($v_13 (x_4 + j) <= 1$ for all $j$).
+ On $A_3$ (demand $(2, 2, 2)$): if $72 in B$, the residual demand $(1, 1, 1)$ across disjoint single-prime supports requires at least $1 + 1 + 1 = 3$ further picks ($|B| >= 4$); if $72 in.not B$, covering $(2, 2, 2)$ with maximum single-prime valuations $(2, 2, 1)$ requires at least $1 + 1 + 2 = 4$ picks (attained by $j in {2, 7, 20, 61}$). Thus $tau(A_3, I) = 4$.
+ On $A_4$ (demand $(4, 2, 2)$): if $72 in B$, residual demand $(3, 1, 1)$ with $v_7 <= 2$ requires at least $ceil(3 / 2) + 1 + 1 = 4$ further picks ($|B| >= 5$); if $72 in.not B$, disjoint demands $(4, 2, 2)$ with caps $(2, 2, 1)$ require at least $2 + 1 + 2 = 5$ picks (attained by $j in {2, 7, 20, 51, 61}$). Thus $tau(A_4, I) = 5$. $square$

*Proposition 3 ($g(5) >= 6$ and $g(6) >= 8$).* Let $x_6 = 581","200","167$ and $I = {x_6 + 1, dots, x_6 + 437}$. Define
$ A_6 = {221, 289, 299, 323, 391, 437} = {13 dot 17, space 17^2, space 13 dot 23, space 17 dot 19, space 17 dot 23, space 19 dot 23}, $
and $A_5 = A_6 without {221} = {289, 299, 323, 391, 437}$. Then $tau(A_5, I) = 6$ and $tau(A_6, I) = 8$.

_Proof._ The active primes are $(13, 17, 19, 23)$, with demand $(2, 5, 2, 3)$ on $A_6$ and $(1, 4, 2, 3)$ on $A_5$. Direct division at the center offset $j = 219$ gives $x_6 + 219 = 581","200","386 = 2 dot 3 dot 59 dot 13 dot 17^2 dot 19 dot 23$, which has valuation vector $(1, 2, 1, 1)$. For every $j in {1, dots, 437} without {219}$, $|j - 219| <= 218 < 13 dot 17 = 221$, so $x_6 + j$ is divisible by at most one prime in ${13, 17, 19, 23}$. Furthermore:
+ Since $17^2 = 289 > 218$ and $17^2 divides (x_6 + 219)$, no $j != 219$ in $I$ is divisible by $17^2$; thus $v_17 (x_6 + j) <= 1$ for all $j != 219$.
+ Since $x_6 + 219 equiv 11 dot 23 = 253 pmod(529)$, the nearest multiples of $23^2 = 529$ lie at $219 - 253 = -34 < 1$ and $219 + 276 = 495 > 437$; thus $v_23 (x_6 + j) <= 1$ for all $j in {1, dots, 437}$.
+ For $p = 13$ and $p = 19$, $j in {128, 297}$ satisfy $v_13 (x_6 + j) = 2$ (with $13^3 = 2197$ absent), and $j = 86$ satisfies $v_19 (x_6 + 86) = 2$ (with $19^3 = 6859$ absent).

Consequently, every element of $I without {x_6 + 219}$ supplies at most one active prime, bounded by $(2, 1, 2, 1)$:
+ On $A_6$ (demand $(2, 5, 2, 3)$): if $x_6 + 219 in B$, the residual demand $(1, 3, 1, 2)$ across disjoint prime supports with $v_17, v_23 <= 1$ requires at least $1 + 3 + 1 + 2 = 7$ additional elements ($|B| >= 8$, attained by $j in {12, 15, 32, 35, 49, 86, 128, 219}$); if $x_6 + 219 in.not B$, covering $(2, 5, 2, 3)$ requires at least $1 + 5 + 1 + 3 = 10$ elements. Hence $tau(A_6, I) = 8$.
+ On $A_5$ (demand $(1, 4, 2, 3)$): if $x_6 + 219 in B$, residual demand $(0, 2, 1, 2)$ requires at least $0 + 2 + 1 + 2 = 5$ additional elements ($|B| >= 6$, attained by $j in {10, 12, 15, 32, 35, 219}$); if $x_6 + 219 in.not B$, covering $(1, 4, 2, 3)$ requires at least $1 + 4 + 1 + 3 = 9$ elements. Hence $tau(A_5, I) = 6$. $square$

*Proposition 4 ($g(7) >= 9$ and $g(8) >= 11$).* Let $P = {41, 43, 47, 53}$ and $Q = {59, 61}$, and set
$ A_8 = P times Q = {2419, 2501, 2537, 2623, 2773, 2867, 3127, 3233}, quad A_7 = A_8 without {2419}, $
with $M = 53 dot 61 = 3","233$. Let $x_8 = 85","145","283","391","654","366","755$ and $I = {x_8 + 1, dots, x_8 + 3233}$. Then $tau(A_8, I) = 11$ and $tau(A_7, I) = 9$.

_Proof._ By the Chinese Remainder Theorem modulo $prod_(p in P union Q) p^2$, $y := x_8 + 1617$ satisfies $y equiv p pmod(p^2)$ for each $p in P$ and $y equiv ((p - 1) / 2) p pmod(p^2)$ for each $p in Q$ (namely $29 dot 59 = 1711 pmod(3481)$ and $30 dot 61 = 1830 pmod(3721)$). Hence $j = 1617$ has valuation $1$ at all six primes in $P union Q$. For every $j in {1, dots, 3233} without {1617}$, $|j - 1617| <= 1616 < 41 dot 43 = 1763$, so $x_8 + j$ is divisible by at most one prime in $P union Q$; moreover, since $1616 < 1711$ and $1616 < 3481 - 1711 = 1770$ (and likewise $1616 < 1830 < 1891$), no multiple of $59^2$ or $61^2$ lies in $I$, giving $v_59 (x_8 + j) <= 1$ and $v_61 (x_8 + j) <= 1$ for all $j$.
+ On $A_8$, the demand is $(2, 2, 2, 2, 4, 4)$. If $1617 in B$, residual demand $(1, 1, 1, 1, 3, 3)$ across disjoint single-prime supports with $v_59, v_61 <= 1$ forces $|B| >= 1 + (1 + 1 + 1 + 1 + 3 + 3) = 11$ (attained by $1617$, $1617 - p$ for $p in P$, and $1617 plus.minus q, 1617 - 2 q$ for $q in Q$). If $1617 in.not B$, each prime in $P$ needs at least $1$ element and each prime in $Q$ needs at least $4$ elements, giving $|B| >= 4 + 8 = 12$. Thus $tau(A_8, I) = 11$.
+ On $A_7 = A_8 without {41 dot 59}$, the demand is $(1, 2, 2, 2, 3, 4)$. Including $1617$ leaves $(0, 1, 1, 1, 2, 3)$, forcing $|B| >= 1 + 8 = 9$; excluding $1617$ forces $|B| >= 1 + 1 + 1 + 1 + 3 + 4 = 11$. Deleting $1617 - 41$ and $1617 + 59$ from the $11$-element cover gives size $9$, so $tau(A_7, I) = 9$. $square$

= Structural Reductions and Cumulative-GCD Slot Packing

Fix $n >= 2$ and a target upper bound $B_n >= n$. To prove $g(n) <= B_n$, suppose by strong induction on $M = a_n$ that $tau(A', I') <= B_n$ holds for all $n$-sets $A'$ with $max(A') < M$, and assume for contradiction that some $A = {a_1 < dots < a_n = M}$ and interval $I = {x + 1, dots, x + M}$ satisfy $tau(A, I) >= B_n + 1$. Among all such counterexamples at maximum $M$, choose $A$ maximizing the sum $sum_(i = 1)^n a_i$.

*Lemma 5 (Interval splitting, divisor-closure maximality, and coprime subadditivity).* Let $(A, I)$ be a sum-maximal counterexample with $tau(A, I) >= B_n + 1$ at $M = a_n$, assuming $g(n - 1) <= B_n - 1$ and $g(k) + (n - k) <= B_n$ for $1 <= k <= n - 1$. Then:
+ _(Minimum element and sub-interval bounds):_ $a_1 > floor(M / B_n)$, and for every $1 <= k <= n - 1$,
  $ a_k > L_(n, k) (M) := ceil((M - (n - k)) / (n - k + 1)) = floor(M / (n - k + 1)). $
+ _(Divisor-closure maximality):_ For every $a_i in A$ and integer $m >= 2$ with $m a_i <= M$, we have $m a_i in A$.
+ _(Common-factor induction):_ $gcd(a_1, dots, a_n) = 1$; in particular no prime divides all $n$ elements of $A$.
+ _(Prime-set and component subadditivity):_ For any partition of the active primes $P(A) = S_1 union.sq S_2$, $tau(A, I) <= tau(D|_(S_1), I) + tau(D|_(S_2), I)$. In particular, if $g(k) + g(n - k) <= B_n$ for all $1 <= k <= n - 1$, then the $n$-vertex graph on $A$ with edges $gcd(a_i, a_j) > 1$ is connected.

_Proof._ (1) Since $g(n - 1) <= B_n - 1$, covering $A without {a_1}$ takes $|B'| <= g(n - 1) <= B_n - 1$ elements of $I$. If $a_1 <= floor(M / B_n)$, then $I$ contains at least $B_n > |B'|$ multiples of $a_1$, leaving an untouched multiple $u in I without B'$ of $a_1$ so that $B' union {u}$ has size $<= B_n$. Similarly, choosing multiples $b_(k + 1), dots, b_n in I$ of $a_(k + 1), dots, a_n$ deletes at most $n - k$ elements from $I$, leaving at most $n - k + 1$ contiguous blocks of total length $>= M - (n - k)$; the longest block $I^*$ has length $>= ceil((M - (n - k)) / (n - k + 1)) = floor(M / (n - k + 1))$. If $a_k <= |I^*|$, covering ${a_1, dots, a_k}$ inside $I^*$ takes $<= g(k)$ elements disjoint from ${b_(k + 1), dots, b_n}$, totaling $<= g(k) + (n - k) <= B_n$.

(2) If $a_i in A$ and $m >= 2$ satisfy $m a_i <= M$ with $m a_i in.not A$, then $m a_i < M$ (as $a_n = M$). Setting $A' = (A without {a_i}) union {m a_i}$ gives $|A'| = n$, $max(A') = M$, $sum A' > sum A$, and $prod A divides m prod A = prod A'$. By sum-maximality, $tau(A', I) <= B_n$, whence $tau(A, I) <= B_n$.

(3) If a prime $p$ divides every $a_i in A$, then $I$ contains $M / p$ consecutive multiples $p(y + 1), dots, p(y + M / p)$ of $p$ ($y = floor(x / p)$). Applying the induction hypothesis at $M / p < M$ to $A / p = {a_1 / p, dots, M / p}$ on ${y + 1, dots, y + M / p}$ and multiplying by $p$ yields a cover of size $<= B_n$.

(4) If $B_1, B_2 subset.eq I$ cover the demands on disjoint prime sets $S_1, S_2$, then $B_1 union B_2$ covers $S_1 union.sq S_2$ with $|B_1 union B_2| <= |B_1| + |B_2|$. $square$

#block(sticky: true)[*Theorem 6 (Universal Cumulative-GCD Slot Theorem and First/Repeat Decomposition).* Let $I$ be any interval of $M$ consecutive positive integers, and let $h_0, h_1, dots, h_(ell - 1) in {1, dots, M}$ ($1 <= ell <= M$).]
+ If $gcd(prod_(i = 0)^(j - 1) h_i, h_j) <= floor(M / (j + 1))$ holds for every $1 <= j < ell$, then there exist distinct elements $b_0, dots, b_(ell - 1) in I$ whose product $prod_(j = 0)^(ell - 1) b_j$ is divisible by $prod_(j = 0)^(ell - 1) h_j$.
+ _(First/Repeat decomposition):_ If each slot is factored as $h_j = f_j g_j <= M$ ($0 <= j < ell$) such that $gcd(prod_(i = 0)^(j - 1) h_i, f_j) = 1$ while $g_j <= floor(M / (j + 1))$, then $gcd(prod_(i < j) h_i, h_j) <= floor(M / (j + 1))$ holds for all $1 <= j < ell$.

_Proof._ (1) Inductively select distinct $b_0, dots, b_(j - 1) in I$ so that $H_(j - 1) := prod_(i = 0)^(j - 1) h_i$ divides $Pi_(j - 1) := prod_(i = 0)^(j - 1) b_i$ (starting with a multiple $b_0 in I$ of $h_0 <= M$). At step $j >= 1$, since $1 <= h_j <= M$, the interval $I$ contains at least one multiple $m in I$ of $h_j$.
- _Case 1 ($m in.not {b_0, dots, b_(j - 1)}$):_ Set $b_j := m$. Since $h_j divides b_j$ and $H_(j - 1) divides Pi_(j - 1)$, we have $H_j = H_(j - 1) h_j divides Pi_(j - 1) b_j = Pi_j$.
- _Case 2 (every multiple of $h_j$ in $I$ lies in ${b_0, dots, b_(j - 1)}$):_ Fix $b_i$ ($0 <= i < j$) with $h_j divides b_i$, so $h_j divides Pi_(j - 1)$. Letting $g_j^* := gcd(H_(j - 1), h_j) <= floor(M / (j + 1))$, both $H_(j - 1)$ and $h_j$ divide $Pi_(j - 1)$, whence $lcm(H_(j - 1), h_j) = (H_(j - 1) h_j) / g_j^*$ divides $Pi_(j - 1)$. Because $|I inter g_j^* ZZ| >= floor(M / g_j^*) >= j + 1$, pigeonhole yields $b_j in I without {b_0, dots, b_(j - 1)}$ divisible by $g_j^*$, giving $H_j = g_j^* lcm(H_(j - 1), h_j) divides b_j Pi_(j - 1) = Pi_j$.

(2) Since $gcd(H_(j - 1), f_j) = 1$, $gcd(H_(j - 1), f_j g_j) = gcd(H_(j - 1), g_j) <= g_j <= floor(M / (j + 1))$. $square$

*Corollary 7 (Two-element absorption and bipartite spanning-forest bound).*
+ For any $n >= 2$, $M = a_n$, and any $a_* in A without {M}$, setting $(h_0, h_1) = (M, a_*)$ satisfies $gcd(M, a_*) <= floor(M / 2)$ (as $a_* < M$ cannot be a multiple of $M$, so $gcd(M, a_*)$ is a proper divisor of $M$); in particular $g(2) = 2$, and covering ${a_*, M}$ uses at most $2$ elements of $I$, leaving $B_n - 2$ disjoint tail slots $[floor(M / 3), dots, floor(M / B_n)]$ for $A without {a_*, M}$.
+ Let $A subset.eq P times Q$ ($|A| = n$) be a subgraph of a complete bipartite semiprime grid on disjoint prime sets $P, Q$ ($|P| = r$, $|Q| = s$), with $max(P union Q) <= floor(M / L)$ where $L := 2 n - r - s + 1$. Then $tau(A, I) <= 2 n - r - s + 1$ for every interval $I$ of length $M$.

_Proof._ Part (1) is immediate from Theorem 6(1) with $ell = 2$. For Part (2), choose a spanning forest $F subset.eq A$ of the bipartite graph $(P union Q, A)$ with $|F| >= r + s - c >= r + s - 1$ edges ($c >= 1$ connected components), ordered so each non-root edge shares at most one endpoint with earlier edges in $F$. Placing the $|F|$ semiprimes of $F$ in slots $0, dots, |F| - 1$ gives $gcd(H_(j - 1), h_j) in {1} union P union Q <= floor(M / L) <= floor(M / (j + 1))$, and placing the remaining $2(n - |F|)$ prime factors of $A without F$ one per slot uses $|F| + 2(n - |F|) = 2 n - |F| <= 2 n - r - s + 1 = L$ slots in Theorem 6(1). $square$

Note that for Proposition 4 ($n = 8$, $r = 4$, $s = 2$), Corollary 7(2) gives $2(8) - 4 - 2 + 1 = 11$, matching $tau(A_8, I) = 11$ with equality; for $K_(2, 3)$ ($n = 6$, $r = 3$, $s = 2$), it gives $2(6) - 3 - 2 + 1 = 8$.

*Lemma 8 (Universal prime-support elimination).* For any prime $P$ dividing $prod A$, write $d_P (A) := |{a in A : P divides a}|$. In a minimal counterexample $(A, I)$ with $tau(A, I) >= B_n + 1$:
+ If $P >= g(n - 1) + 1$, then $d_P (A) != 1$ (and similarly $D_q (A) != 1$ for any prime $q >= g(n - 1) + 1$).
+ If $P >= B_n$ and $g(n - 2) + 3 <= B_n$, then $d_P (A) != 2$.

In particular: (i) for $(n, B_3) = (3, 4)$ ($M >= 10$), no prime $P >= 5$ divides $prod A$; (ii) for $(n, B_4) = (4, 5)$ ($M >= 14$), every prime $P >= 7$ dividing $prod A$ has $d_P (A) = 3$ (and $D_5 (A) != 1$); (iii) for $(n, B_5) = (5, 6)$ ($M >= 14$), every prime $P >= 7$ dividing $prod A$ has $d_P (A) in {2, 3, 4}$ (and $D_7 != 1$); and (iv) for $(n, B_6) = (6, 8)$ ($M >= 22$), every prime $P >= 11$ dividing $prod A$ satisfies $3 <= d_P (A) <= 5$, and $D_7 (A) != 1$.

_Proof._ (1) Suppose $d_P (A) = 1$, with $a_i = s_i P^e <= M$ ($P divides.not s_i$). Then $s_i <= M / P$, so $floor(M / s_i) >= P >= g(n - 1) + 1$. Let $B' subset.eq I$ ($|B'| <= g(n - 1)$) cover $A without {a_i}$, and let $b_i in I$ be a multiple of $a_i$. If $b_i in.not B'$, then $B' union {b_i}$ covers $A$ in $<= g(n - 1) + 1 <= B_n$ picks; if $b_i in B'$, then since $P divides.not prod_(r != i) a_r$, $b_i$ already supplies $P^e$ free of conflict while $I without B'$ contains an untouched multiple $u$ of $s_i$, so $B' union {u}$ covers $A$ in $<= g(n - 1) + 1 <= B_n$ picks.

(2) Suppose $d_P (A) = 2$, with $a_i = s_i P^(e_i)$ and $a_j = s_j P^(e_j)$ ($1 <= e_i <= e_j$, $P divides.not s_i s_j$). Because $a_i != a_j$ are two distinct multiples of $P^(e_i)$ in $[1, M]$, we have $2 P^(e_i) <= max(a_i, a_j) <= M$, so $|I inter P^(e_i) ZZ| >= 2$. Also $s_i, s_j <= M / P <= M / B_n$, giving $floor(M / s_i), floor(M / s_j) >= B_n$. Let $B'' subset.eq I$ ($|B''| <= g(n - 2) <= B_n - 3$) cover $A without {a_i, a_j}$ (which is coprime to $P$), let $b_j in I$ be a multiple of $s_j P^(e_j)$, and put $B_P = {b_j}$ if $P^(e_i + e_j) divides b_j$ or $B_P = {b_j, m_2}$ for $m_2 in (I inter P^(e_i) ZZ) without {b_j}$ otherwise.
+ If $b_j in.not B''$, then $B'' union B_P$ has size $<= (B_n - 3) + 2 = B_n - 1$ and covers $s_j P^(e_i + e_j) prod_(r in.not {i, j}) a_r$; adjoining one untouched multiple of $s_i$ (from the $>= B_n$ in $I$) gives size $<= B_n$.
+ If $b_j in B''$, then $|B'' union B_P| <= (B_n - 3) + 1 = B_n - 2$ covers $P^(e_i + e_j) prod_(r in.not {i, j}) a_r$; adjoining two distinct untouched multiples of $s_j$ and $s_i$ (from the $>= B_n$ of each in $I$) gives size $<= B_n$. $square$

*Lemma 9 ($g(d)$-subset tail decoupling).* Suppose a prime $P$ divides exactly $d in {3, dots, n - 1}$ elements of $A$, and write $A_P = {P c_1 < dots < P c_d}$ with $P divides.not c_1 dots.c c_d$. Then $I$ contains a subset $B_1 subset.eq I inter P ZZ$ of size $|B_1| <= g(d)$ covering $prod_(a in A_P) a$. Consequently, if $prod_(a in A without A_P) a$ factors into $B_n - g(d)$ integers bounded by $floor(M / (g(d) + 1)), dots, floor(M / B_n)$, then sequential untouched multiples in $I without B_1$ cover $A$ in $<= B_n$ elements.

_Proof._ Setting $k = floor(x / P)$, the first $c_d <= floor(M / P)$ multiples of $P$ in $I$ are $P(k + 1), dots, P(k + c_d)$. Applying the definition of $g(d)$ to ${c_1, dots, c_d}$ on ${k + 1, dots, k + c_d}$ yields $B'_1$ of size $<= g(d)$ covering $c_1 dots.c c_d$; setting $B_1 = {P y : y in B'_1} subset.eq I$ supplies $P^d c_1 dots.c c_d$ (if $|B'_1| < d$, pad $B'_1$ to size $d <= g(d)$ inside ${k + 1, dots, k + c_d}$, since $c_d >= d$). Each tail factor $h_r <= floor(M / (g(d) + r))$ ($1 <= r <= B_n - g(d)$) has $>= g(d) + r$ multiples in $I$, leaving an untouched multiple outside the $<= g(d) + r - 1$ previously chosen points. $square$

= Finite Certificates and Analytic Closure for $3 <= n <= 6$

*Lemma 10 (Closed-form descending factor-packing bound).* Let $C_1 >= C_2 >= dots >= C_t >= 1$ be slot capacities, and let $Q = prod_(q in S) q^(e_q)$ be a product of prime factors sorted in nonincreasing order. If greedy placement of each prime factor $q$ into the tightest (largest-index) bin $k$ with $B_k q <= C_k$ fails, let $p in S$ be the first prime factor that fails to fit. When $p <= C_t$, every bin $B_k$ contains only primes $>= p$ and satisfies $B_k p > C_k$, so $B_k >= max(floor(C_k / p) + 1, p)$ for all $1 <= k <= t$, forcing
$ prod_(q in S, space q >= p) q^(e_q) >= T_(C_1, dots, C_t) (p) := p prod_(k = 1)^t max(floor(C_k / p) + 1, p). $
Hence if $T_(C_1, dots, C_t) (p) > prod_(q in S, space q >= p) q^(e_q)$ holds for every $p in S$ (with $p <= C_t$), greedy packing into $(C_1, dots, C_t)$ cannot fail. Note also that among $n$ distinct positive integers in $[1, M]$, the $p$-part for the largest prime $p_"max" = max(S)$ has $n$ distinct cofactors $>= 1, 2, dots, n$, so $p_"max"^(e_(p_"max")) <= M^n / n!$.

*Theorem 11 (Exact values $g(3) = 4$, $g(4) = 5$, and $g(5) = 6$).* We have $g(3) = 4$, $g(4) = 5$, and $g(5) = 6$.

_Proof._ Lower bounds are proved in Propositions 2 and 3. For the upper bounds:
+ _$g(3) <= 4$:_ By Lemma 8(i), for $M >= 10$ every prime $P >= 5$ is eliminated ($d_P in {1, 2}$ by Lemma 8, $d_P = 3$ by Lemma 5(3)), leaving only ${2, 3}$-smooth sets. On capacities $(M, floor(M / 2), floor(M / 3), floor(M / 4))$, $T(2) > M^3$ and $T(3) > M^3 / 6$ hold for all $M >= 184$, and direct Chinese Remainder verification checks all $4 <= M <= 183$ ($0$ counterexamples).
+ _$g(4) <= 5$:_ By Lemma 8(ii), for $M >= 14$ every prime $P >= 7$ dividing $prod A$ has $d_P (A) = 3$. If no prime $>= 7$ divides $prod A$ (${2, 3, 5}$-smooth), capacities $(M, dots, floor(M / 5))$ satisfy $T(2), T(3) > M^4$ and $T(5) > M^4 / 24$ for all $M >= 9","702$, and finite search checks all ${2, 3, 5}$-smooth $M <= 9","701$. Otherwise, let $P_1 = max S_7 (A) >= 7$ (with $d_(P_1) (A) = 3$) and let $x_1$ be the unique element of $A without A_(P_1)$:
  - If $P_1 > floor(M / 4)$, then $v_(P_1) (a) = 1$ for all $a in A_(P_1)$ and the three cofactors satisfy $1 <= c_1 < c_2 < c_3 <= 3$, forcing ${c_1, c_2, c_3} = {1, 2, 3}$. Any $3$ consecutive multiples of $P_1$ in $I$ cover $P_1^3 dot 6$ in $3$ picks, leaving $2$ tail slots $[floor(M / 4), floor(M / 5)]$ for the ${2, 3, 5}$-smooth element $x_1 < M$ (closed by Lemma 10 for $M >= 120$).
  - If $P_1 <= floor(M / 4)$ and $v_(P_1) (a) <= 1$ on $A_(P_1)$: when $x_1 <= floor(M / 2)$, Lemma 5(1) gives $x_1 >= a_1 > floor(M / 5)$, so $P_1 x_1 > 7(M / 5) > M$; hence $I$ contains a multiple $b_0$ of $x_1$ with $P_1 divides.not b_0$, which is automatically disjoint from the $g(3) = 4$ cover $B_1 subset.eq I inter P_1 ZZ$ of $A_(P_1)$ supplied by Lemma 9. When $x_1 > floor(M / 2)$, Corollary 7(1) absorbs $(M, a_3)$ in $2$ picks and leaves tail slots $[floor(M / 3), floor(M / 4), floor(M / 5)]$ for $a_1 a_2 < M^2$ (closed by Lemma 10 for $M >= 7","345$, and checked below $7","345$ via @bergstrom26smallcode).
  - If $P_1^2 divides a$ for some $a in A_(P_1)$, then $P_1 <= sqrt(M)$ and every prime dividing $prod A$ lies in $[2, sqrt(M)]$; absorbing $(M, a_3)$ via Corollary 7(1) and packing $a_1 a_2 < M^2$ into $[floor(M / 3), floor(M / 4), floor(M / 5)]$ closes all $M >= 7","345$ (and finite verification checks $M <= 7","344$ @bergstrom26smallcode).
+ _$g(5) <= 6$:_ By Lemma 5(3) and Lemma 8(iii), for $M >= 14$ every prime $P >= 7$ dividing $prod A$ has $d_P (A) in {2, 3, 4}$. On ${2, 3, 5}$-smooth sets ($|S_7 (A)| = 0$), Lemma 10 on $(M, dots, floor(M / 6))$ closes all $M >= 20","001$. When $S_7 (A) != emptyset$ with $P_1 = max S_7 (A)$:
  - If $d_(P_1) (A) in {3, 4}$ and $v_(P_1) <= 1$, Lemma 9 decouples $A_(P_1)$ in $g(d_(P_1)) in {4, 5}$ picks inside $I inter P_1 ZZ$, leaving $6 - g(d_(P_1)) in {1, 2}$ tail slots $[floor(M / (d_(P_1) + 2)), dots, floor(M / 6)]$ for the remaining $5 - d_(P_1)$ elements.
  - If $d_(P_1) (A) = 2$ (which requires $P_1 = 7$ by Lemma 8(2)) or $v_(P_1) >= 2$ ($P_1 <= sqrt(M)$), Corollary 7(1) absorbs $(M, a_4)$ in $2$ picks and packs $a_1 a_2 a_3 < M^3$ into $[floor(M / 3), dots, floor(M / 6)]$.
  All remaining finite configurations below the analytic thresholds are verified via @bergstrom26smallcode ($0$ counterexamples). $square$

*Theorem 12 (Exact value $g(6) = 8$).* For every $6$-element set $A subset.eq ZZ_(>= 2)$ and every interval $I$ of $max(A)$ consecutive positive integers, $tau(A, I) <= 8$. Combined with Proposition 3, $g(6) = 8$.

_Proof._ Assume $(A, I)$ is a minimal counterexample at $M = a_6$. Table 2 summarizes the certified parameters across both regimes.
1. _Finite regime ($7 <= M <= 3","481$):_ For $7 <= M <= 63$, exhaustive enumeration of all GCD-connected, divisor-closed $6$-sets surviving Lemma 5(1) verifies $tau(A, I) <= 8$ across all residue profiles modulo $prod p^(e_p)$ ($15","709$ universal-$x$ Chinese Remainder leaves; @bergstrom26smallcode). For $64 <= M <= 3","481$, every prime $P > floor(sqrt(M))$ satisfies $v_P (a) <= 1$ and hence $d_P (A) in {0, 3, 4, 5, 6}$ by Lemma 8(iv); partitioning candidate sets into the six large-prime multiplicity patterns $emptyset$, $(3)$, $(4)$, $(5)$, $(6)$, and $(3, 3)$ with $(L(x), x)$ smooth-bucket pruning, Lemma 9 tail decoupling, and Theorem 6 Cumulative-GCD packing certifies all $3","418$ values $64 <= M <= 3","481$ ($3$ Chinese Remainder leaves at $M in {72, 80}$ and $0$ residual leaves across $81 <= M <= 3","481$, pruning $24","628","129","260$ search branches in the accompanying certificate archive @bergstrom26smallcode).

2. _Analytic regime ($M >= 3","482$):_ Let $S_11 (A) = {p >= 11 : p divides prod A}$. By Lemma 5(3) and Lemma 8(iv), every $P in S_11 (A)$ satisfies $3 <= d_P (A) <= 5$, and $D_7 (A) != 1$. We split into three exhaustive cases:
   - *Case 1 ($|S_11 (A)| = 0$, ${2, 3, 5, 7}$-smooth sets):* On $(M, floor(M / 2), dots, floor(M / 8))$, Lemma 10 gives $T(p) > M^6$ for $p in {2, 3, 5}$ and $T(7) > M^6 / 720$ for all $M >= 56","125$. For $3","482 <= M <= 56","124$, there are exactly $354$ #box[${2, 3, 5, 7}$-smooth] values of $M$, all verified computationally via @bergstrom26smallcode.
   - *Case 2 ($|S_11 (A)| = 1$, $S_11 (A) = {P_1}$):* If $P_1^2 divides a$ for some $a in A$, then $P_1 <= sqrt(M)$, covered under the bounded-prime reduction of Subcase 3b below; otherwise $v_(P_1) (a) <= 1$ for all $a in A$ with $d = d_(P_1) (A) in {3, 4, 5}$, and the $6 - d$ elements of $A without A_(P_1)$ are ${2, 3, 5, 7}$-smooth in $(floor(M / 8), M)$:
     - $d = 5$ ($g(5) = 6$, tail $[floor(M / 7), floor(M / 8)]$): for every $M >= 3","137$ and prime $q <= sqrt(M)$, $q(floor(M / (7 q)) + 1)(floor(M / (8 q)) + 1) > M^2 / (56 q) >= M^(3 / 2) / 56 > M >= x_1$.
     - $d = 4$ ($g(4) = 5$, tail $[floor(M / 6), floor(M / 7), floor(M / 8)]$): Lemma 10 closes all $M >= 16","465$ ($T(2), T(3), T(5) > M^2$, $T(7) > M^2 / 2$), and every ${2, 3, 5, 7}$-smooth pair $(x_1, x_2)$ on $[3482, 16464]$ is verified at the monotone lower endpoint $M_"min" = max(3482, x_2)$ @bergstrom26smallcode.
     - $d = 3$ ($g(3) = 4$, tail $[floor(M / 5), dots, floor(M / 8)]$): Lemma 10 closes all $M >= 576","241$, and every divisor-closed ${2, 3, 5, 7}$-smooth triple $(x_1, x_2, x_3)$ up to $576","240$ is verified at $M_"min" = max(3482, x_3)$ @bergstrom26smallcode.
   - *Case 3 ($|S_11 (A)| >= 2$):* Let $P_1 = max S_11 (A) >= 13$.
     - *Subcase 3a ($P_1 > floor(M / 8)$):* Since $P_1 >= floor(M / 8) + 1 > M / 8$, we have $11 P_1 > 8 P_1 > M$; thus no prime $>= 11$ other than $P_1$ can divide any element of $A_(P_1)$, and $P_1^2 > M$. Pick any $P_2 in S_11 (A) without {P_1}$; since $d_(P_1) (A) >= 3$, $d_(P_2) (A) >= 3$, and $A_(P_1) inter A_(P_2) = emptyset$, we must have $|A_(P_1)| = |A_(P_2)| = 3$ and $A = A_(P_1) union.sq A_(P_2)$. Writing $A_(P_1) = {P_1 c_1, P_1 c_2, P_1 c_3}$, the strict inequality $8 P_1 > M$ forces $1 <= c_1 < c_2 < c_3 <= 7$, so $c_1 c_2 c_3 <= 5 dot 6 dot 7 = 210 <= floor(M / 8)$ (for $M >= 1","680$). Applying Lemma 9 to $P_2$ yields $B_2 subset.eq I inter P_2 ZZ$ covering $A_(P_2)$ in $|B_2| <= g(3) = 4$ picks. Because $P_1 P_2 >= 11 P_1 > M$, no element of $I$ is divisible by $P_1 P_2$, so $B_2$ contains zero multiples of $P_1$. Since $I$ contains $>= floor(M / P_1) >= c_3 >= 3$ multiples of $P_1$, adjoining any $3$ distinct multiples of $P_1$ in $I$ (automatically disjoint from $B_2$) plus $1$ untouched multiple of $c_1 c_2 c_3 <= floor(M / 8)$ covers $A$ in $<= 4 + 3 + 1 = 8$ picks.
     - *Subcase 3b ($P_1 <= floor(M / 8)$):* Every prime dividing $prod A$ satisfies $p <= floor(M / 8)$, and since $(M^(1 / 4))^4 = M$ with $M^(1 / 4) > 7.68$ for $M >= 3","482$, every element $a_i <= M$ has at most $3$ prime factors (with multiplicity) in $cal(L) := {p divides prod A : p > M^(1 / 4)} subset.eq S_11 (A)$. Because $D_p (A) >= d_p (A) >= 3$ for every $p in cal(L)$, we obtain
       $ 3 |cal(L)| <= sum_(p in cal(L)) D_p (A) <= 3 n = 18, $
       so $|cal(L)| <= 6$ and $sum_(p in cal(L)) D_p (A) <= 18$. Three steps close all remaining configurations:
       1. _First-appearance and repeat slots:_ Order $cal(L) = {q_1, dots, q_r}$ ($2 <= r <= 6$) by nonincreasing $D_p (A)$, and assign each $q_k$ a distinct first-appearance slot $fs(q_k) in {0, dots, 7}$ so that $f_(fs(q_k)) := q_k^(min(D_(q_k), floor(log_(q_k) M))) <= M$ (setting $f_j = 1$ on unused slots). For any repeat demand $c_k := D_(q_k) - min(D_(q_k), floor(log_(q_k) M)) >= 1$ (which occurs only when $q_k <= sqrt(M)$ and $c_k <= 2$), assign $q_k^(c_k)$ to a repeat factor $g_j$ with $j > fs(q_k)$. Since $q_k^2 <= M / 8$ whenever $c_k = 2$ (as $q_k^3 <= M$ for $D_(q_k) >= 3$ and $q_k > M^(1 / 4)$ forces $q_k^2 < M^(2 / 3) <= M / 8$ for $M >= 512$) and $q_k <= floor(M / 8)$ whenever $c_k = 1$, every repeat factor satisfies $q_k^(c_k) <= floor(M / 8) <= floor(M / (j + 1))$ for all $j <= 7$. Whenever two primes $q_a, q_b in cal(L)$ co-occur in the same slot $j$, we pair primes sharing an element of $A$ (so $q_a q_b <= M$, ensuring $f_j g_j <= M$), or apply Lemma 9 to $P_1$ when $cal(L) = {P_1, P_2}$ has multiplicity pattern $(3, 3)$ (covering $A_(P_1)$ in $g(3) = 4$ picks and packing $u_1 u_2 u_3$ into $[floor(M / 5), floor(M / (6 P_1)), floor(M / (7 P_1)), floor(M / (8 P_1))]$). Thus Theorem 6(2) covers the entire $cal(L)$-part in $8$ slots with residual capacities $C_j = floor(M / (f_j g_j))$ ($0 <= j <= 7$).
       2. _Small-prime capacity bound:_ Let $S_"sm" := {p divides prod A : p <= M^(1 / 4)}$. If greedy packing of $S_"sm"$ into $(C_0, dots, C_7)$ fails at a first failing prime $q in S_"sm"$, Lemma 10 gives
          $ prod_(p in S_"sm", space p >= q) p^(e_p) >= q prod_(j = 0)^7 (floor(C_j / q) + 1) > q prod_(j = 0)^7 (M / (f_j g_j q)) = M^8 / (q^7 prod_(j = 0)^7 f_j g_j). $
          Because each $f_j g_j$ absorbs at most one denominator factor $j + 1$ in the worst-case alignment and $q <= M^(1 / 4)$, this forces $prod_(p in S_"sm", space p >= q) p^(e_p) > M^8 / ("40,320" q^7) >= M^(25 / 4) / "40,320"$, exceeding $M^6$ for all $M > "40,320"^4$.
       3. _Large-$M$ threshold and finite check:_ To reduce the threshold below $"40,320"^4$, absorb $(M, a_5)$ in $2$ picks via Corollary 7(1) and pack the remaining $4$ elements $a_1 a_2 a_3 a_4 < M^4$ into the $6$ tail slots $C'_j = floor(M / ((j + 3) f'_j g'_j))$ ($0 <= j <= 5$). Defining $T_6 (M, q) := q prod_(j = 0)^5 max(floor(C'_j / q) + 1, q)$ across all valid $cal(L)$-allocations $(f'_j, g'_j)$ and primes $q <= M^(1 / 4)$, we have $T_6 (M, q) > M^4$ for all $M >= 360","065$ (since $M^6 / ("20,160" q^5) >= M^(19 / 4) / "20,160" > M^4$ once $M > "20,160"^(4 / 3) approx 554","000$, and direct evaluation of the floor product lowers the exact cutoff to $360","065$). All remaining configurations with $3","482 <= M <= 360","064$ are verified computationally via @bergstrom26smallcode ($0$ counterexamples). $square$

#figure(
  table(
    columns: (1.2fr, auto, 1.3fr),
    inset: (x: 5pt, y: 4pt),
    align: (left, right, left),
    stroke: 0.5pt,
    [*Verified Quantity*], [*Certified Value*], [*Verification Method*],
    [Exact value $g(4)$ ($M = 143$, $x_4 = 631","559$)], [$5$], [Proposition 2 + Theorem 11 finite/analytic closure],
    [Exact value $g(5)$ ($M = 437$, $x_6 = 581","200","167$)], [$6$], [Proposition 3 + Theorem 11 finite/analytic closure],
    [Exact value $g(6)$ ($M = 437$, $x_6 = 581","200","167$)], [$8$], [Proposition 3 + Theorem 12 hybrid proof],
    [Constructive lower bounds $g(7), g(8)$ ($M = 3","233$)], [$>= 9, space >= 11$], [Proposition 4 asymmetric $K_(2, 4)$ CRT witness at $x_8$],
    [Certified finite $g(6) <= 8$ range $M$], [$7 .. 3","481$ ($3","475$ rows)], [Exhaustive CRT + Cumulative-GCD certificate @bergstrom26smallcode],
    [Universal-$x$ CRT leaves ($7 <= M <= 80$)], [$15","712$], [$0$ residual CRT leaves across $81 <= M <= 3","481$],
    [Slot-pruned search branches ($7 <= M <= 3","481$)], [$24","628","129","260$], [Smooth-bucket + Lemma 9 + Theorem 6 pruning @bergstrom26smallcode],
    [${2, 3, 5, 7}$-smooth $M in [3482, 56124]$], [$354$ values], [Lemma 10 closed-form + monotone smooth bridges @bergstrom26smallcode],
  ),
  caption: [Summary of certified small-$n$ bounds, finite search invariants, and analytic closure thresholds.],
)

#set heading(numbering: none)

= Data and Code Availability

The finite verification certificate for $7 <= M <= 3","481$ and the standalone zero-dependency Rust and independent arbitrary-precision verification suites reproducing Propositions 2–4 and Theorems 11–12 are archived at Zenodo @bergstrom26smallcode (`https://doi.org/10.5281/zenodo.24366897`), with the following SHA-256 digests:
#[
  #set par(justify: false)
  - Uncompressed $3","475$-row certificate ($169","969$ bytes): \ `65b22b54e7f3b652a20d1812ede4cd7664f12c5d230338fea9608acbd9792e68`
  - Zstandard-compressed certificate archive ($17","418$ bytes): \ `b6368979558724d0b7934a329419a34c610cb8e25e428cba9eb758842ae11b45`
  - Standalone Rust verifier source: \ `cd2cb340e3d768ba03cd309126df035d83a0f7ccc46d9016c45152e9d885fb98`
  - Independent arbitrary-precision verifier source: \ `4430203d277d0ab41f5a75bd63610a7996bcf9268bd183eab5388b9851082c3a`
]

= Acknowledgments and Declaration of Generative AI

During the preparation of this work, the author used internal research automation (Karen, 24x AI Research) and large language model assistance (Google Gemini) for witness construction, structural lemma exploration, verification software implementation, and manuscript editing. After using these tools, the author reviewed, verified, and edited the content as needed and takes full responsibility for the mathematical correctness and content of the publication.

#bibliography("references.bib", title: "References")
