# An exact compact-group model for residue densities in Erdős 335

Owner proof draft for #506, 2026-11-10. The additional hypothesis in this packet is that every residue section of each summand has an ordinary density. The original problem allows sections without a density. The first theorem below gives a precise reduction with this extra hypothesis. The last corollary completes the case of two irrational summand densities under that hypothesis.

## Definitions and inputs

Let \(\Omega=\widehat{\mathbb Z}\) with normalized Haar measure \(\mu\). For \(E\subset\mathbb N\) let \(F_E\) denote its closure in \(\Omega\). Then
\[
b^*(E)=\inf_{m\ge1}\frac{|R_m(E)|}{m}=\mu(F_E),
\]
where \(b^*\) is upper Buck density and \(R_m(E)\) is the actual set of residues met by E. Indeed the periodic preimages of \(R_{n!}(E)\) decrease to \(F_E\) and are cofinal among these periodic covers. In particular \(\overline d(E)\le b^*(E)\). For nonempty A,B, compactness and density give \(F_{A+B}=F_A+F_B\). See Hennecart, [Kneser's theorem for upper Buck density](https://arxiv.org/html/2410.13275v2), for the terminology and residue limits.

Two forms of Kneser are used. For nonempty integer sets with \(\underline d(X+Y)<\underline d(X)+\underline d(Y)\), the positive-integer tail of \(X+Y\) is ultimately periodic. See [Griesmer 2026, Theorem 1.1](https://arxiv.org/html/2602.19014v1) for the correctly printed statement. Only this periodicity conclusion is needed. For measurable sets \(P,Q\) in a compact abelian group, if \(m_*(P+Q)<m(P)+m(Q)\), then their literal sumset is a union of cosets of a compact open subgroup. See [Griesmer 2014, Proposition 1.1](https://arxiv.org/html/1112.6403v3). Literal periodicity in this strict alternative matters.

The integer version implies that for any nonempty integer sets with ordinary densities x,y,
\[
\underline d(X+Y)\ \ge\ \min(x+y,b^*(X+Y)).
\tag{1}
\]
If the left side is less than x+y, the tail periodicity implies that its ordinary density equals its upper Buck density. Finitely many exceptional elements have Buck density zero, as is also seen by refining the period. This argument includes x or y equal to zero. All uses below concern sets bounded below, so a finite shift to nonnegative integers is harmless.

## 1. The measure model

Assume A and B are nonempty, with ordinary densities \(\alpha,\beta\), and that \(d(A\cap\{n:n\equiv r\bmod m\})\) and its B analogue exist for every m,r. Set \(s=\alpha+\beta\), and write \(C=A+B\). We first prove
\[
m_*(\mathcal A+\mathcal B)\le \underline d(C)
\tag{2}
\]
for two explicitly constructed sets \(\mathcal A,\mathcal B\subset\Omega\times\mathbb T\) with masses \(\alpha,\beta\) and projections exactly \(F_A,F_B\). Here m is product Haar measure.

Put \(q_n=n!\) and use the increasing finite sigma algebras of its residue cosets. On a coset r modulo \(q_n\) define
\[
a_n(\omega)=q_n\,d(A\cap\{x:x\equiv r\bmod q_n\}),
\qquad
f_n(\omega)=q_n\,\mu(F_A\cap(r+q_n\Omega)).
\]
Both functions lie in [0,1]. Finite additivity of the ordinary section limits makes \(a_n\) a bounded martingale. The functions \(f_n\) are conditional expectations of \(1_{F_A}\) and converge to it almost everywhere since these cosets generate the Borel sigma algebra. Let \(a(\omega)=\lim_n a_n(\omega)\) at points where that limit exists and \(f_n(\omega)\to1\), and set it to zero elsewhere. Bounded martingale convergence gives \(\int a=\alpha\), because \(a_n=0\) on unoccupied cosets and a point outside the closed \(F_A\) eventually lies in an unoccupied coset. Define \(b,b_n,g_n\) similarly for B.

For \(u\in[0,1]\) let \(I_u\subset\mathbb T\) be the closed arc from 0 to u, with \(I_0=\{0\}\) and \(I_1=\mathbb T\). Define
\[
\mathcal A=\{(\omega,z):\omega\in F_A,\ z\in I_{a(\omega)}\},
\qquad
\mathcal B=\{(\eta,z):\eta\in F_B,\ z\in I_{b(\eta)}\}.
\]
These sets are Borel. They retain the point at height zero even on a residue support where the density is zero. Consequently the projection of their sumset is exactly \(F_A+F_B\). The sumset is analytic in the metrizable compact product, hence Haar measurable. Its fiber over \(\gamma\) is the union, over all \(\omega+\eta=\gamma\) with \(\omega\in F_A,\eta\in F_B\), of arcs \(I_{\min(1,a(\omega)+b(\eta))}\).

Take a sequence of prefix lengths realizing \(\underline d(C)\). Pass to a diagonal subsequence \(N_k\) on which the count ratios for every C residue section converge. For each \(q_n\) use these limits to define the bounded martingale \(c_n\) by the same normalization as \(a_n\). Its almost-everywhere limit c has integral \(\underline d(C)\).

Fix any \(\gamma\) at which \(c_n(\gamma)\to c(\gamma)\), and any \(\omega\in F_A,\eta\in F_B\) with \(\omega+\eta=\gamma\). At level \(q_n\), let X,Y be the two actual sections rescaled by \(q_n\) and shifted to integer origins. They are nonempty because their cosets meet the literal sets. They have ordinary densities \(a_n(\omega),b_n(\eta)\). Their upper Buck densities equal \(f_n(\omega),g_n(\eta)\). Indeed multiplication by \(q_n\) is a homeomorphism from \(\Omega\) onto \(q_n\Omega\), and the closure of a section is the intersection of the closed carrier with its open coset. The rescaled section sum, with a fixed carry shift, lies in the corresponding C section. Thus (1) and the fact that a fixed translate of either summand is contained in its sumset give
\[
c_n(\gamma)\ \ge\
\min\big(a_n(\omega)+b_n(\eta),\,b^*(X+Y)\big),
\qquad
b^*(X+Y)\ge\max(f_n(\omega),g_n(\eta)).
\tag{3}
\]
The first inequality holds because \(c_n(\gamma)\) is a subsequential relative density of that C section, whereas (1) bounds the lower ordinary density of the section sum.

If either \(a(\omega)>0\) or \(b(\eta)>0\), the corresponding closed-carrier fraction tends to 1 by the chosen version of a or b. The liminf of \(a_n(\omega)+b_n(\eta)\) is at least \(a(\omega)+b(\eta)\), including when a zero value was assigned at a nonconvergence point. Taking limits in (3) yields
\[
c(\gamma)\ge \min(1,a(\omega)+b(\eta)).
\]
When both values are zero this follows from nonnegativity. This holds for every representation of the fixed \(\gamma\), so the fiber length is at most \(c(\gamma)\). Integrating proves (2). No assertion about arbitrary subsequence densities of the input sections was used in (3). Their ordinary limits are the hypothesis that makes that step available.

## 2. Equality and output residue densities

If \(\underline d(C)=s\), then \(m(\mathcal A+\mathcal B)=s\). Otherwise compact Kneser gives literal periodicity of this sumset under a compact open K. Every such K in \(\Omega\times\mathbb T\) contains \(\{0\}\times\mathbb T\), since the image of the connected circle in the finite quotient is trivial. The sumset would then be \((F_A+F_B)\times\mathbb T\), with measure \(b^*(C)\ge s\), a contradiction.

When \(d(C)=s\), every residue section of C has an ordinary density too. To see this, start with any sequence of prefix lengths and take a diagonal subsequence on which all C section counts have limits. The argument for (2) now applies on this subsequence, with \(\int c=s\), and the fiber lengths of \(\mathcal A+\mathcal B\) are bounded by c almost everywhere. Their integrals agree, so the fiber lengths equal c almost everywhere. Hence each section limit equals the mass of \(\mathcal A+\mathcal B\) above that residue coset, which is independent of the chosen subsequence. Every sequence has such a subsequence, proving the ordinary section limits.

The compact sets in this argument encode marginal residue densities and literal profinite supports. They are auxiliary sets. They do not assert that A or B is the pullback of a compact-group set.

## 3. The inverse reduction when \(b^*(C)>s\)

Assume both input densities are positive and \(d(C)=s\) with \(b^*(C)>s\). Apply [Griesmer 2014, Theorem 1.3](https://arxiv.org/html/1112.6403v3) to \(\mathcal A,\mathcal B\). The theorem applies to measurable positive-mass sets with inner sumset measure equal to the sum of their masses. These conditions follow from Sections 1 and 2.

An open subgroup K of the product is \(H\times\mathbb T\) for an open subgroup H of \(\Omega\). Every such H has the form \(h\Omega\): it contains some \(q_n\Omega\), and the subgroup in the cyclic quotient lifts to \(h\Omega\).

* In the periodic alternative, \(\mathcal A+K=(F_A+H)\times\mathbb T\) agrees with \(\mathcal A\) in measure, and similarly for B. Since the closed \(F_A\) fills its occupied H cosets in measure, it equals their union, and \(\mathcal A\) is full in each of those product cosets up to measure zero. The same holds for B. A fixed point from each occupied coset on one side and a full-measure section on the other side fill the corresponding output coset in measure. The resulting sumset mass is \(b^*(C)\), contrary to \(b^*(C)>s\).
* In the extendible alternative, a larger pair has larger mass sum and the same sumset measure s. Compact Kneser makes the larger sumset literally periodic, so it contains full circle fibers over \(F_A+F_B\), again contradicting \(b^*(C)>s\).

There remain the interval alternative and the quasi-periodic alternative.

In the interval alternative, both model sets lie in cosets of \(H\times\mathbb T\), each filling the inverse image of a positive-length arc in measure under a continuous surjection to \(\mathbb T\). The surjection is nontrivial on the circle factor. Otherwise it factors through the profinite H and has finite image: the preimage of a sufficiently short neighborhood of zero contains an open subgroup, whose image is a subgroup in an arc containing no nontrivial subgroup. Hence each of these arc preimages has the same positive vertical fiber measure above every point in the corresponding H coset. Literal containment and equality of measures then force \(F_A\) and \(F_B\) to be the full corresponding H cosets, since they are closed and have full measure there.

Thus A and B each lie in one residue class modulo h, and after affine rescaling both meet every residue class. Their rescaled density sum is \(hs<1\), since the upper Buck density of C is \(1/h\). One may use positive indices throughout by writing elements as \(hk-r\) with \(k\ge1\) and \(0\le r<h\). Apply [Ackelsberg--Richter, Theorem 1.4](https://arxiv.org/html/2604.12864v1) to the rescaled pair. Its internal modulus must be 1 because its first summand meets every residue class. The degenerate case with internal modulus 1 would give zero second density. Therefore both rescaled sets are literal subsets of parallel closed Bohr intervals, filling the interval pullbacks up to density zero.

In the quasi-periodic alternative, \(\mathcal A_0,\mathcal B_0\) are each in one K coset and the background parts are full up to measure zero in their occupied K cosets. The background of either side is disjoint from the active coset on that side, because its K enlargement is disjoint from its exceptional part. The chosen active pieces therefore equal the actual restrictions of the model sets to their active cosets. The same argument with closed supports and fiber measures shows that the original A and B fill their background residue classes up to density zero. Both have a literal nonempty section in the active class, even if that section has density zero.

Write \(S=R_h(A), T=R_h(B)\), with active residues i,j and \(W=S+T\). The output residue \(i+j\) has just this one expression in \(S+T\), by the unique-expression clause of the compact theorem. Every other occupied output residue is full up to density zero in the original sumset. For each such residue some representation uses a full background section and a nonempty section on the other side. One fixed element from the latter translates the former. The same reasoning in the model gives full measure in every other occupied output coset. Equality of model masses on the active sum, together with total equality, gives
\[
|W|=|S|+|T|-1.
\tag{4}
\]
Explicitly, if x,y are the rescaled active input densities, then the total input mass is \((|S|+|T|-2+x+y)/h\), and the total model sum mass is \((|W|-1+x+y)/h\). The exact same output splitting in the integers now shows that the rescaled active pair has ordinary sumset density x+y. Its input residue sections again have ordinary densities because they correspond to further residue sections of the original sets.

The difference between upper Buck density and ordinary density is multiplied by h on passing to the active pair. Indeed the other \(|W|-1\) output classes are full in density and hence fill their entire closed H cosets. The active closed carrier scales from the closure of the active sumset. Thus if \(\Delta=b^*(C)-s>0\), the new difference is \(h\Delta\). In the quasi-periodic alternative \(h\ge2\), since there is a nonempty background on at least one side. Since any such difference is at most 1, there are at most \(\lfloor\log_2(1/\Delta)\rfloor\) successive quasi-periodic reductions with both input densities positive.

These steps reach either the interval alternative or an active pair with at least one zero input density. In the latter case a separate result about the literal sum of the sparse section with its partner is required. The squares example in lemmas_20261110T2218Z.md explains why invariance under fixed translations does not supply that result.

## 4. Complete restricted consequence for two irrational densities

Suppose all input residue sections have ordinary densities and both input densities are irrational. If \(b^*(A+B)=\alpha+\beta\), the ordinary equality follows from the integer Kneser argument in lemmas_20261110T2006Z.md. If \(b^*(A+B)<\alpha+\beta\), equality is impossible.

In the remaining strict case, equality holds exactly for the pairs admitting the finite decomposition just described with the following terminal data. Each quasi-periodic step has relatively full background sections, one nonempty active residue per side, a unique active output expression, and the finite identity (4). The terminal pair lies in two residue classes of a common modulus and after rescaling consists of literal subsets filling parallel Bohr interval pullbacks up to density zero, with positive lengths summing below 1.

For necessity, the reductions preserve irrationality of both input densities: the next density is h times the previous density minus the integer number of full background classes. Thus no zero-density terminal case occurs. For sufficiency at the terminal pair, the literal interval containments give the upper bound on the sumset density by equidistribution. The full-density fillings have positive density in every residue class, again by equidistribution on each progression. A strict lower-density deficit would give an ultimately periodic sumset missing an actual residue class after refinement, which is impossible when the summands meet all residue classes. The terminal density therefore equals the sum. At each preceding step, the unique active expression and the full background output classes give the exact output density, and (4) matches it to the sum of the input densities.

This conclusion includes arbitrary modular obstructions within its residue-density hypothesis. It does not supply that hypothesis for an arbitrary equality pair, and it leaves sparse active cases when an input density becomes zero. These are the two outstanding gaps toward the original problem.

## Checks and attribution

The continuum digital example is consistent with the theorem. Its model has two full output classes and a third class supported only at height zero. In the actual equality member the third output section has density zero, and the reduction terminates with two zero-density sections. The other members have extra ordinary density in that third class. This checks why the model's small sumset alone cannot imply the original equality.

The quasi-periodic compact inverse theorem and the all-residue-class integer theorem are borrowed with their stated hypotheses. The new argument in this packet is the explicit martingale transfer and its consequences for residue sections. It neither imports the rejected automatic model bridge nor claims an independent proof audit of the source papers. No novelty claim is made.

