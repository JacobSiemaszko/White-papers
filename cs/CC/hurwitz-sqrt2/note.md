# An N^{√2+o(1)} upper bound for Hurwitz's sum-of-squares problem from the ETH-refutation construction

**Jakub Piotr Siemaszko** · 7 November 2026 · research note, not peer-reviewed · v0.3 · DOI [10.5281/zenodo.24024947](https://doi.org/10.5281/zenodo.24024947)

> **Reader's note from the author.** I do not understand the mathematics in this note. It was written by Claude, an AI model, during a session in which I was asking it about something else. I am not a mathematician. I am publishing it because the claim is precise and checkable, and so that people who can judge it, can. What I did myself: I ran the two scripts and they print what the note says. If you find an error, please open an issue; I will mark the note as corrected or withdrawn.
>
> **Status and provenance.** This note derives a consequence of Theorem B of the paper *A $`2^{o(n)}`$ Time Algorithm for 3-SAT* (Claude / Anthropic, 26 Oct 2026). That theorem is machine-checked in Lean 4 by its authors but has, at the time of writing, not been independently verified by a human. The mathematical content of this note was produced by Claude (Anthropic) — Claude Sonnet 5.5 (reasoning effort: high) for the literature survey and first attempts, Claude Fable 5.1 (reasoning effort: extra high) for Proposition 1, the Theorem, the scripts and this text — in a session on 6–7 Nov 2026 directed by the author, who is not a mathematician and makes no claim to have verified the mathematics himself. It came up as a by-product of a different question. What the author did check is stated in §9: running the scripts of §6 and §7. The construction is entirely the ETH paper's; the observation is that its own Appendix G remark, applied to Theorem B instead of Lemma 2, improves the best known Hurwitz upper bound. Nothing here bears on P vs NP.

## 1. Result

Let $`B_{\mathbb Q}(N)`$ be the least $`s`$ such that

```math
\Big(\sum_{i=1}^N x_i^2\Big)\Big(\sum_{j=1}^N y_j^2\Big)=\sum_{k=1}^{s} f_k\,f_k'
```

for bilinear forms $`f_k,f_k'`$ in $`x,y`$ over $`\mathbb Q`$ (Hrubeš's $`\beta_{\mathbb Q}(N)`$; HWY's $`B_{\mathbb Q}(\mathrm{SOS}_N)`$), and let $`\sigma_{\mathbb C}(N)`$ be the same with squares $`f_k^2`$ over $`\mathbb C`$.

**Theorem.** $`B_{\mathbb Q}(N)\le N^{\sqrt2+o(1)}`$ and $`\sigma_{\mathbb C}(N)\le N^{\sqrt2+o(1)}`$, with $`\sqrt2\approx1.4143`$.

The best previously published bound is $`O(N^{c})`$ with $`c=1+2H(\alpha/2)\approx1.615`$, where $`H(\alpha)=1/2`$ (Hrubeš, CCC 2024, Theorems 1 and 12). Hrubeš's bound also holds in every positive characteristic; the bound here holds over $`\mathbb Q`$, over $`\mathbb C`$, and over fields of characteristic $`p>h(N)=O(\log^2N)`$, since the identity has integer coefficients after multiplication by $`h!`$.

## 2. Definitions (from the ETH paper)

Write $`N=2^\lambda`$. The *crossing* is $`X(x,y,u,v)=[x=v][y=u]`$ on $`(\{0,1\}^\lambda)^4`$.

*Row-wise* a function $`F(x,y,u,v)`$ is the matrix with row index $`(x,y)`$ and column index $`(u,v)`$; *column-wise*, row index $`(x,u)`$ and column index $`(y,v)`$. The crossing is a permutation matrix of rank $`N^2`$ in both. $`F`$ *factors through $`c`$ bits* in a direction (Definition 1) if that matrix is a product of two integer matrices with inner dimension $`2^c`$; equivalently it is a sum of $`2^c`$ functions of rank 1 in that direction.

*Pieces with parameters $`(\rho,c)`$* (Definition 7), for $`\tfrac12\le\rho<1`$: for every $`\lambda`$, an integer $`d\ge1`$, an index set $`I`$ with $`|I|\le(2\lambda)^c`$, and integer functions $`A_i`$ with

```math
\sum_{i\in I}A_i=d\,[x=v][y=u],\qquad c_i^{\mathrm{row}}+c_i^{\mathrm{col}}\le4\rho\lambda+c\log(2\lambda),
```

where $`A_i`$ factors row-wise through $`c_i^{\mathrm{row}}`$ and column-wise through $`c_i^{\mathrm{col}}`$ bits. Theorem A turns pieces with parameter $`\rho`$ into a #k-SAT algorithm with time $`2^{O(km/(\log m)^{\alpha'})}`$, $`\alpha'=\log_2(1/\rho)`$. Theorem B gives pieces with $`\rho=1/\sqrt2`$.

*$`P(N)`$* (Naslund; ETH paper, Appendix G) is the least number of rational-valued functions, each of row-wise or of column-wise rank 1, summing to the crossing. By HWY11 Lemma 3.5 this is the width over $`\mathbb Q`$ of the non-commutative polynomial $`\sum_{i,j}x_iy_jx_iy_j`$: a row-rank-1 function $`g(x,y)h(u,v)`$ is form (a) of that lemma, a column-rank-1 function $`H(x,u)g(y,v)`$ is form (b). By HWY11 Proposition 4.1,

```math
B_{\mathbb Q}(N)\le P(N)\le 4\,B_{\mathbb Q}(N),
```

and by HWY11 Remark 1.5, $`\sigma_F\le3B_F`$ over any algebraically closed $`F`$ of characteristic $`\ne2`$ (via $`2zz'=(z+z')^2+(iz)^2+(iz')^2`$).

## 3. Proposition 1: from pieces to $`P(N)`$

**Proposition 1.** If pieces with parameters $`(\rho,c)`$ exist, then for all $`N=2^\lambda`$

```math
P(N)\le\sum_{i\in I}\min\big(2^{c_i^{\mathrm{row}}},2^{c_i^{\mathrm{col}}}\big)\le(2\lambda)^{3c/2}\,N^{2\rho}.
```

Hence $`\rho\ge\tfrac12\liminf_N\log_NP(N)`$, and any improvement of $`\rho`$ improves the Hurwitz bound.

*Proof.* Row-wise, $`A_i`$ is a sum of at most $`2^{c_i^{\mathrm{row}}}`$ row-rank-1 functions; column-wise, of at most $`2^{c_i^{\mathrm{col}}}`$ column-rank-1 functions. Take the cheaper representation for each $`i`$ and divide by $`d`$. For the second inequality, $`\min(c_i^{\mathrm{row}},c_i^{\mathrm{col}})\le\tfrac12(c_i^{\mathrm{row}}+c_i^{\mathrm{col}})\le2\rho\lambda+\tfrac c2\log(2\lambda)`$ and $`|I|\le(2\lambda)^c`$. $`\square`$

*Remarks.* (i) The ETH paper performs exactly this step for its Lemma 2 (Appendix G: "by taking the $`A_i`$ with $`i<t/2`$ row-wise and the others column-wise"), obtaining $`P(N)=O(N^{11/6})`$, which is weaker than Hrubeš; it does not apply it to Theorem B. (ii) The floor $`\rho\ge\tfrac12`$ is noted in the paper's Appendix H via rank subadditivity and is not claimed here. (iii) Proposition 1 is the converse of the paper's remark that $`P(N)\le N^{c}`$ yields two pieces with rank product $`N^{2+c}`$, i.e. $`\rho=(2+c)/4`$.

## 4. Theorem: $`P(N)\le N^{\sqrt2+o(1)}`$

*The pieces of Theorem B.* For given $`\lambda`$ let $`h\ge2`$ be least with $`p(h)\ge2^\lambda`$, $`p`$ the partition function. A string $`x`$ names a partition $`\mu(x)`$ of $`h`$. The paper takes $`d=h!`$, $`I=\{-2h,\dots,2h\}`$ and pieces $`A_s`$ (its (53)) with $`\sum_sA_s=h!\,[x=v][y=u]`$. Its formulas (54) and (55) write $`A_s`$ explicitly as

- row-wise, a sum of $`R_s^{\mathrm{row}}=\sum_{i=0}^{2h}p(s+i)`$ products $`F(x,y)\,G(u,v)`$;
- column-wise, a sum of $`R_s^{\mathrm{col}}=\sum_{i=0}^{2h}p(2h-s-i)`$ products $`F(x,u)\,G(y,v)`$;

with $`p(E)=0`$ for $`E<0`$. The substitution $`i\mapsto2h-i`$ gives $`R_s^{\mathrm{col}}=R_{-s}^{\mathrm{row}}`$, and $`R_s^{\mathrm{row}}`$ is non-decreasing in $`s`$, so

```math
\min\big(R_s^{\mathrm{row}},R_s^{\mathrm{col}}\big)=R_{-|s|}^{\mathrm{row}}=\sum_{j=0}^{2h-|s|}p(j).
```

**Theorem.** For $`N=2^\lambda`$,

```math
P(N)\le\sum_{s=-2h}^{2h}\sum_{j=0}^{2h-|s|}p(j)=\sum_{j=0}^{2h}(4h-2j+1)\,p(j)\le(2h+1)(4h+1)\,p(2h)=N^{\sqrt2+o(1)}.
```

*Proof.* The first inequality is Proposition 1 applied to the $`A_s`$ with the exact counts above. The equality counts, for each $`j`$, the $`s`$ with $`|s|\le2h-j`$. The last inequality uses that $`p`$ is non-decreasing. For the asymptotics, the paper's (46) (Hardy–Ramanujan) gives $`c_{HR}\sqrt h\le\lambda+O(\log\lambda)`$ with $`c_{HR}=\pi\sqrt{2/3}/\ln2\approx3.70`$ and $`\log_2p(E)\le c_{HR}\sqrt E+C_{HR}`$; hence $`\log_2p(2h)\le\sqrt2\,c_{HR}\sqrt h+C_{HR}\le\sqrt2\,\lambda+O(\log\lambda)`$, and $`h=O(\lambda^2)`$. $`\square`$

*Explicit form.* Reading each term of (54) or (55) commutatively (the four positions $`x,y,v,u`$ are of types $`X,Y,X,Y`$, so $`F(x,y)G(u,v)\mapsto F(X,Y)\,G(Y,X)`$ and $`H(x,u)g(y,v)\mapsto H(X,Y)\,g(Y,X)`$, both products of bilinear forms) gives

```math
h!\,\Big(\sum_ix_i^2\Big)\Big(\sum_jy_j^2\Big)=\sum_{k}f_kf_k'
```

with integer bilinear forms, all computable in time $`2^{O(\lambda)}`$ (Definition 7(c)).

## 5. Corollaries

1. $`B_{\mathbb Q}(N)\le P(N)\le N^{\sqrt2+o(1)}`$. For $`N`$ not a power of two, pad to $`N'\le2N`$.
2. $`\sigma_{\mathbb C}(N)\le3B_{\mathbb Q}(N)\le N^{\sqrt2+o(1)}`$.
3. Over $`\mathbb R`$ there is no improvement, since $`2zz'=(z+z')^2-(z-z')^2`$ needs a minus sign; cf. arXiv 2605.00590 on base-field dependence of Hurwitz's problem. Over $`\mathbb F_p`$ with $`p`$ fixed there is no improvement either, because the scaling factor $`h!`$ vanishes for $`p\le h`$.

| Quantity | Field | Known upper bound | This note |
| --- | --- | --- | --- |
| $`B_{\mathbb Q}(N)`$ (products) | $`\mathbb Q`$ | $`O(N^{1.616})`$, Hrubeš 2024 Thm 12 | $`N^{\sqrt2+o(1)}`$ |
| $`\sigma_{\mathbb C}(N)`$ (squares) | $`\mathbb C`$ | $`O(N^{1.616})`$, Hrubeš 2024 Thm 1 | $`N^{\sqrt2+o(1)}`$ |
| $`\sigma_{\mathbb R}(N)`$ | $`\mathbb R`$ | $`O(N^2/\log N)`$ | unchanged |
| any, char $`p`$ fixed | $`\mathbb F_p`$ | $`O(N^{1.616})`$ | unchanged |
| lower bounds | all | $`B\ge N/2`$; $`\sigma(N)>N`$ for $`N\notin\{1,2,4,8\}`$ | unchanged |

## 6. Numerical check of the exponent

`check_exponent.py` evaluates the exact sum $`\sum_s\min(R_s^{\mathrm{row}},R_s^{\mathrm{col}})`$ with partition numbers from Euler's pentagonal recurrence. The exponent $`\log_2(\text{sum})/\lambda`$ drops below Hrubeš's $`1.615`$ around $`\lambda\approx70`$ and converges to $`\sqrt2`$ like $`\log\lambda/\lambda`$.

| $`\lambda`$ | $`h`$ | $`\log_2`$ sum | exponent |
| --- | --- | --- | --- |
| 20 | 61 | 38.4 | 1.922 |
| 60 | 372 | 98.5 | 1.641 |
| 80 | 620 | 127.8 | 1.598 |
| 120 | 1295 | 185.8 | 1.549 |
| 200 | 3361 | 300.9 | 1.505 |
| 400 | 12663 | 586.4 | 1.466 |
| 600 | 27849 | 870.9 | 1.451 |

The limit $`\sqrt2`$ follows from the proof; the table only confirms direction and rate.

## 7. Independent instance check

`check_instance.py` implements the construction of Appendix B from scratch (the operators $`a[r]`$ of (47), $`a_\mu`$ and $`b_\mu`$ of Lemma 10, $`Q_s`$ of (48), the pieces $`A_s`$ of (53)) in exact integer arithmetic and, for small $`\lambda`$, verifies

1. the operator of (47) against the recursion (O2);
2. Lemma 10, $`a_\mu[-h]\,b_\nu=h!\,[\mu=\nu]`$;
3. Lemma 9(a), invariance of $`Q_s`$ under exchanging the factors (sampled);
4. the crossing identity $`\sum_sA_s=h!\,[x=v][y=u]`$ on all $`N^4`$ inputs;
5. the term counts $`R_s^{\mathrm{row}},R_s^{\mathrm{col}}`$ of (54)/(55) against the formulas in §4;
6. the resulting Hurwitz identity $`h!\,(\sum x_i^2)(\sum y_j^2)=\sum_kf_kf_k'`$ as an exact polynomial identity in $`2N`$ variables.

Result for $`\lambda=2`$ ($`N=4`$, $`h=4`$, $`d=24`$): all six checks pass; the identity uses $`307`$ products over $`\mathbb Z`$. (At such small $`N`$ the count is of course far above $`N^2`$; the construction is asymptotic and only overtakes Hrubeš's bound near $`\lambda\approx70`$.) This makes the translation in §4 independent of the Lean development for the instances checked; it does not verify Theorem B in general.

## 8. Relation to Naslund's problem and to the ETH method

Let $`\gamma=\liminf\log_NP(N)`$ and $`\rho^{\ast}=\inf\{\rho:\text{pieces with parameter }\rho\text{ exist}\}`$. Then

```math
\tfrac12\gamma\le\rho^{\ast}\le\tfrac1{\sqrt2},\qquad1\le\gamma\le\sqrt2,\qquad\alpha'_{\max}=\log_2(1/\rho^{\ast})\le1-\log_2\gamma.
```

- Naslund's Problem 12 asks whether $`P(N)\ge N^{1+\varepsilon}`$. A positive answer gives $`\alpha'\le1-\log_2(1+\varepsilon)<1`$: the tensor method of the ETH paper would then be capped strictly below $`\alpha'=1`$, and the running time $`2^{O(m/\log m)}`$ would be out of its reach.
- Conversely, pushing the method to $`\alpha'\to1`$ (i.e. $`\rho\to\tfrac12`$) would prove $`P(N)\le N^{1+o(1)}`$ and refute Naslund. The paper's Appendix H describes the route: a graded space with $`\log\dim V_E\sim E^{\alpha}`$ gives $`\rho=2^{\alpha-1}`$; partitions give $`\alpha=\tfrac12`$. Any $`\alpha<\tfrac12`$ improves the Hurwitz bound; $`\alpha\to0`$ would refute Naslund.
- By HWY11, a lower bound $`\sigma_{\mathbb C}(N)\ge N^{1+\varepsilon}`$ implies exponential lower bounds for non-commutative arithmetic circuits computing the permanent. This note shrinks the admissible range of such an $`\varepsilon`$ from $`(0,0.615]`$ to $`(0,0.414]`$; it does not help prove one.

## 9. What has and has not been checked

Checked by the model (Claude Fable 5.1), reading the sources during the session: the definitions and counts in the ETH paper (Definitions 1, 5, 7; Lemma 2; Theorem A, B; (46), (53)–(56); Appendices G, H); HWY11 Lemma 3.5, Proposition 4.1 and Remark 1.5; Hrubeš's exponent $`1+2H(\alpha/2)`$; and it wrote and ran the scripts of §6 and §7.

Checked by the author (Jakub Piotr Siemaszko): that `check_instance.py --lam 2` and `check_exponent.py` run on his machine and print the results reported in §6 and §7. The author has not verified the mathematical argument and does not claim to.

Not checked: Theorem B in general (Lean-verified by its authors, with AI-written and AI-reviewed Lean code; no human is known to have checked it); whether this observation was made elsewhere between 26 Oct and 7 Nov 2026 (searches found nothing).

## Sources

- Claude (Anthropic), *A $`2^{o(n)}`$ Time Algorithm for 3-SAT*, 26 Oct 2026. https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/paper.pdf
- P. Hrubeš, *A Subquadratic Upper Bound on Sum-of-Squares Composition Formulas*, CCC 2024, LIPIcs 300, 12:1–12:11. https://drops.dagstuhl.de/storage/00lipics/lipics-vol300-ccc2024/LIPIcs.CCC.2024.12/LIPIcs.CCC.2024.12.pdf
- P. Hrubeš, A. Wigderson, A. Yehudayoff, *Non-commutative circuits and the sum-of-squares problem*, J. Amer. Math. Soc. 24 (2011), 871–898; ECCC TR10-021. https://eccc.weizmann.ac.il/report/2010/021/
- E. Naslund, *The partition rank of a tensor and k-right corners in $`\mathbb F_q^n`$*, Problem 12 (cited via the ETH paper).
- *The Hurwitz sum-of-squares problem depends on the base field*, arXiv 2605.00590 (2026). https://arxiv.org/abs/2605.00590

*License: this text is released under CC BY 4.0; the scripts in this folder under the repository's MIT license.*
