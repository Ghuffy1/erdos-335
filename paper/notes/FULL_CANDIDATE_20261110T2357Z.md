# Candidate full characterization of Erdős problem 335

Owner proof packet, #506, 2026-11-10. The theorem below covers arbitrary positive ordinary input densities, all literal modular obstructions, and the boundary \(\alpha+\beta=1\). Its last alternative is a parametrization by exact residue masks on consecutive intervals, a density condition on those masks alone, and a finite family of interval-endpoint packing tests. The proof and the adequacy of this last form as a classification await independent ROOT review.

## The characterization

Let \(A,B\subset\mathbb N\) have positive ordinary densities \(\alpha,\beta\), and let \(s=\alpha+\beta\). For a modulus q, let \(R_q(E)\) denote the set of residues actually met by E. Define from the two inputs
\[
\gamma=\inf_{q\ge1}\frac{|R_q(A)+R_q(B)|}{q}.
\]
The ordinary density \(d(A+B)\) exists and equals s if and only if either \(\gamma=s\), or \(\gamma>s\) and at least one of the following three descriptions applies. When \(\gamma<s\) equality is impossible.

### 1. Parallel intervals in the exceptional residue classes

For some h let \(S=R_h(A)\), \(T=R_h(B)\), with distinguished \(i\in S,j\in T\). The A classes in \(S\setminus\{i\}\) and B classes in \(T\setminus\{j\}\) fill their respective classes up to ordinary density zero. The output residue \(i+j\) has a unique expression in \(S+T\), and
\[
|S+T|=|S|+|T|-1.
\tag{1}
\]
After rescaling the exceptional sections to positive integers, they are literal subsets of the pullbacks of two positive-length closed arcs under the same irrational circle rotation. Each fills its pullback up to density zero, and the arc lengths sum to less than 1. The modulus h may be 1.

### 2. A singleton exceptional section

There are the same literal finite conditions as in (1). One exceptional section consists of exactly one element. The other exceptional section has a positive ordinary relative density less than 1 and is otherwise unrestricted. The roles of A and B may be exchanged.

### 3. Residue masks with sparse transitions

For some M, define the exact masks in block k by
\[
S_k=\{r\in\{0,\ldots,M-1\}:Mk+r\in A\},\qquad
T_k=\{r\in\{0,\ldots,M-1\}:Mk+r\in B\},\qquad k\ge0.
\]
The pair \((S_k,T_k)\) changes at \(o(N)\) of the first N block boundaries. In the finite cyclic group of order M define
\[
U_k=(S_k+R_M(B))\cup(R_M(A)+T_k).
\]
The following two tests on the input masks and their run endpoints must hold.

- The ordinary mean of \(|U_k|/M\) equals s.
- For each \(w\in\{0,\ldots,M-1\}\), the maximum packing size described below is \(o(N)\).

The packing test uses the maximal consecutive integer intervals on which the pair of input masks is constant. For three such runs \(I=[a,b]\), \(J=[c,d]\), \(K=[e,f]\), and residues r in the A mask of I and t in the B mask of J, put \(w=(r+t)\bmod M\) and \(\kappa=\lfloor(r+t)/M\rfloor\). If w is absent from the constant mask \(U_k\) on K, form the interval
\[
[a+c+\kappa,b+d+\kappa]\cap K\cap[0,N-1].
\tag{2}
\]
Empty intersections are omitted. An infinite right endpoint is allowed. For the given w the packing size is the maximum sum of lengths of pairwise disjoint intervals (2). Only finitely many runs can contribute for any N. Length here counts integer points.

This third description can be used to generate pairs. Choose a finite modulus and a sequence of constant-mask runs with sublinear transition count. Read the two positive ordinary input densities from the mask means. The additional conditions use the same-time finite masks and an interval packing test on the given endpoints. No density of an unknown sumset occurs in any of the three descriptions. The last test retains literal singleton and sparse runs, which can create density in the sum.

## Proof of the numerical branch and of the first two descriptions

The literal output has residue support \(R_q(A)+R_q(B)\) at q, so \(\gamma=b^*(A+B)\). The upper ordinary density is at most \(\gamma\). If \(\gamma=s\) and the lower ordinary density were less than s, integer Kneser would make the output ultimately periodic, so its lower ordinary density would equal its upper Buck density, a contradiction. This proves the numerical branch and excludes \(\gamma<s\). [Griesmer, Theorem 1.1](https://arxiv.org/html/2602.19014v1)

In description 1, the two exceptional summands have density sum equal to their arc-length sum, and their sum has at most that density by literal interval containment and equidistribution. They meet every residue class after rescaling. Integer Kneser excludes a lower-density deficit, so the active output has the desired density. In description 2 the active output is a fixed translate of the positive-density active input. In both cases every other output class is full up to density zero, since it has a representation using one full background and one nonempty actual section. The unique active expression and (1) give exactly the ordinary total \(s\).

In particular the boundary \(s=1\) falls entirely under the numerical branch. It says that \(A+B\) must meet every residue class at every modulus. A direct complementary-template analysis of the failing boundary case is in [the boundary reduction](lemmas_20261110T2006Z.md).

## The structural input for the remaining necessity proof

Assume \(d(A+B)=s<\gamma\). Use \(\Delta=\gamma-s\), \(\delta_A=b^*(A)-\alpha\), \(\delta_B=b^*(B)-\beta\). The following components are proved in the cited owner packets.

- [Local deficit compensation](local_deficit_compensation_20261110T2246Z.md) starts with Ackelsberg–Richter's actual cyclic windows. A fixed finite modular deficit forces the window summand to be full in measure on a bounded-modulus mask. The compensating extra residue is controlled by fixed literal representatives and the ordinary window totals.
- [Positive templates and common asymptotic periods](common_asymptotic_period_20261110T2349Z.md) proves that \(\delta_A,\delta_B>\Delta\) gives description 1, including rational input densities. It applies Griesmer's inverse theorem to exact Loeb models when local finite deficit tends to zero, uses literal Buck gaps to bound iteration, and identifies the same one partial coset in both local orientations. The finite set of possible templates and vanishing increments of prefix counts give one ordinary global profile. The actual positive active pair meets every residue class after rescaling, so Ackelsberg–Richter provides literal interval containment. This packet also proves common shift invariance under a fixed M when both input gaps are positive and their minimum is at most \(\Delta\).
- [One Buck-regular summand](one_buck_regular_summand_20261110T2342Z.md) proves that if one \(\delta\) is zero, some summand is periodic in density. Its auxiliary compact model works with an arbitrary subsequential profile of the other summand, using fixed translates and a 0-or-1 profile on the first side.
- [One periodic summand](periodic_summand_exact_reduction_20261110T2330Z.md) proves that in the last case either both summands and the output are periodic in density, or there is the exact finite template (1) with one literal sparse exceptional section, the other of positive density, and an active sum which agrees in density with each fixed translate of the positive active section.

The proof of common asymptotic periods in the second packet did not yet establish the following additional fact, which is needed for this theorem.

## Finite translates cover the degenerate output in density

Suppose first that both input gaps are positive and their minimum is at most \(\Delta\). Start from any sequence of macro prefix lengths and choose common intermediate-scale windows, as in the [local proof](common_asymptotic_period_20261110T2349Z.md). In every fixed local ultralimit the input and output window totals are \(\alpha,\beta,s\). We claim that at least one of the two actual window inputs is periodic in measure at some finite modulus.

A fixed local modular deficit gives this immediately by compensation. An exact Loeb pair with essentially periodic output also gives it by the local periodic-output argument. A positive terminal is excluded by the gap inequality (3) of the local proof. A zero window terminal is already periodic in measure. Consequently, if neither actual window input were periodic, the two local orientations would both end with a zero prefix section and a positive window section.

In this latter situation the two actual prefixes on \([1,H_k]\) would have periodic profiles in the same ultralimit, at their respective terminal moduli. Write their full masks at a common multiple \(\ell\) as P and Q. Fixed literal translates show that the C prefix fills
\[
(P+R_\ell(B))\cup(R_\ell(A)+Q).
\tag{3}
\]
The size of this union cannot be smaller than \(|P|+|Q|\). Otherwise the finite completion lemma forces all literal output residues into the union, contradicting \(\gamma>s\). Its size is at most \(s\ell=|P|+|Q|\) by the ordinary C total. Thus the C prefix profile is periodic and (3) exactly fills its ordinary mass.

At least one of the two individual baselines in (3) also fills this mass. To see this, suppose \(R_\ell(A)+Q\) has smaller mass. Apply the strict periodic-input reduction of Section 1 of the [local proof](common_asymptotic_period_20261110T2349Z.md) to these prefix windows, with B as the periodic input. Its argument needs only the local totals and fixed literal translations, both valid for these prefixes. It gives at some h a full B background \(T_1\), the exact literal A support S, one exceptional A class of positive mass x, and a C base \(S+T_1\) plus one extra active class. The A prefix is periodic at its original modulus. At a common refinement, every class of S contains at least one full A prefix class, because each has positive mass. The literal B support contains every finer residue inside \(T_1\), since those B prefix sections fill their classes. The opposite baseline \(P+R_\ell(B)\), read at a common refinement, therefore fills the entire base \(S+T_1\). A fixed actual B element in the sparse class also translates the active A prefix mask into the extra class and contributes its whole mass x. Thus the opposite baseline has mass at least s and at most s, as claimed. Refining the period does not change the mass of either baseline, since the full mask lifts to all finer residues and the other support is literal.

On the other hand, a zero prefix B terminal at modulus h has B full on its prefix background \(T_1\), A window relative mass \(x\in(0,1)\) in one active class and full mass elsewhere in its occupied backgrounds. Hence \(sh\) is an integer plus x and is not an integer. The B-prefix baseline \(R_h(A)+T_1\) has mass a multiple of \(1/h\) and is strictly below s, since the C prefix has ordinary total s. The reverse zero-prefix terminal would likewise make the A-prefix baseline strictly below s. This contradicts the preceding saturation assertion. The claim follows.

We can now use the local periodic-input reduction in every such window. In its strict-base case, the output backgrounds are filled by fixed actual representatives of the nonperiodic summand and the full periodic window sections. One fixed actual element in the sparse residue of the periodic-window summand translates the positive active section to fill the only remaining output section in measure. The modulus h is at most \(1/\delta_A\) or \(1/\delta_B\), according to the periodic side. In its periodic-output case, if one baseline is smaller, the same strict-base argument in that orientation applies. If both baselines saturate, Section 1 of the local proof gives periodic local inputs and output at a coarsened modulus \(h\le1/\Delta\). The output then fills in measure by fixed representatives and the periodic window masks at that h.

Let \(D=\lceil\max(1/\Delta,1/\delta_A,1/\delta_B)\rceil\), and take finite actual sets \(F_A\subset A,F_B\subset B\) containing one representative of every literal class at every \(h\le D\). These choices are independent of the prefix sequence, the window start and the ultrafilter. The preceding local arguments give
\[
C\ \sim_d\ (A+F_B)\cup(F_A+B),
\tag{4}
\]
where \(E\sim_d F\) means \(d(E\triangle F)=0\). In detail, failure of the normalized difference count to tend to zero on common good windows would give a discrepant window sequence and ultralimit. At that limit one local periodic-input reduction fills the entire C window from the chosen representatives, a contradiction. The finite translates only incur bounded endpoint shifts. Averaging good-window counts and using the arbitrary macro sequence establishes the ordinary zero difference in (4).

When one input Buck gap is zero, use the periodic-summand reduction. If both summands and C are periodic in density, the exact periodic-output identity from [the periodic theorem](lemmas_20261110T2218Z.md) gives (4) from one representative of each literal residue at the common period. If the sparse terminal has one point, description 2 applies. Otherwise the positive active section agrees in density with its translate by the difference-gcd of the literal sparse active section, as explained in the periodic-summand proof. Thus A and B have a common asymptotic period after multiplying by the quotient modulus. Equation (4) again holds by the full background classes and one actual shift for the active class.

We have proved that every remaining equality pair has a common M such that \(A+M\sim_d A\), \(B+M\sim_d B\), and (4). Its exact paired masks change at sublinearly many block boundaries by the shift discrepancy count.

## Exact mask formula and interval criterion

The following facts are elementary and apply to any two inputs with common M-shift invariance in density.

In (4) one can use one actual representative of each literal residue modulo M. If an existing representative b and its replacement have the same residue, their shifts differ by a fixed integer multiple of M. The density-zero shift discrepancy shows that the two translates of A agree in density. Do the same for A representatives and B translates. If the new selection contains additional residues, its union still lies in the literal C, so (4) remains true.

The resulting finite union agrees in density with the set of integers having block masks \(U_k\). Indeed a fixed shift \(b=Mq+t\) adds residue t and shifts the temporal block index by q plus the carry 0 or 1. The exact input masks at two block indices with any fixed difference agree outside a density-zero set of indices, by sublinear transition count. Thus each such translate has the predicted shifted residue mask at the same time, up to density zero. A finite union over the representatives gives precisely \(U_k\) in density. This also shows, without assuming (4), that the mask set \(U\) is contained in the literal output up to density zero.

It follows that (4) implies the mean condition in description 3. It also implies the packing condition. For clarity, for a fixed output residue w the intervals in (2) are exactly the block-index intervals represented outside \(U_k\) by sums with that residue. Each source run contains every block index between its endpoints with the stated r or t occupied. Therefore all integer indices between the two endpoint sums, including the carry, are achieved by that source pair. Conversely every literal representation uses two source runs and one target run, giving one of these intervals. These statements use the exact mask of every block, including singleton runs and all initial exceptions.

Conversely, for a finite family of integer intervals, the length of its union is at most three times the maximum total length of a disjoint subfamily. To prove this, greedily choose a longest remaining interval and discard all intervals meeting it. Each discarded interval has at most the chosen length and lies within the enlargement by that length on both sides. The chosen intervals are disjoint, and their enlargements cover the whole union with total length at most three times their original total length. Thus the packing test implies that the block indices represented outside \(U_k\) have count \(o(N)\) in each residue. The finite-frame containment just proved gives the reverse inclusion up to density zero. Consequently \(C\sim_d U\), and the mean condition gives ordinary \(d(C)=s\). This proves sufficiency of description 3 and completes the claimed characterization.

## Source scope and group-model issue

The cyclic transfer at intermediate scales is borrowed from [Ackelsberg–Richter, Theorems 8.7 and 9.1](https://arxiv.org/html/2604.12864v1). The whole-pair density and literal containment conclusions of their Theorem 1.4 are used only after rescaling the positive active pair and proving it meets every residue class. The exact Loeb inverse and iteration are borrowed from [Griesmer, Proposition 10.2, Corollary 10.4 and Lemma 10.14](https://arxiv.org/html/1807.01694v3). The compact Haar inverse in the zero Buck-gap argument is [Griesmer, Theorem 1.3](https://arxiv.org/html/1112.6403v3). Finite Kneser, local compensation, gap comparisons, the two-orientation matching, finite-frame saturation and the endpoint characterization are stated with their separate hypotheses in the linked proofs. The July White/Claude [working report](https://www.erdosproblemaday.com/report/335) is credited for its earlier ultimately periodic finite-prefix criterion.

The random subset of even integers in [Ackelsberg–Richter, Example 1.6](https://arxiv.org/html/2604.12864v1) is in the numerical branch. Thus the classification includes equality pairs with no proposed interval structure. The [irregular equality example](irregular_residue_equality_20261110T2244Z.md) has genuine oscillating residue densities and is covered by the interval-run description. The [digital example](lemmas_20261110T2006Z.md) keeps all marginal residue data and literal residue supports fixed while changing the output density. This explains why an exact classifier must retain an additional condition on sums from the literal sparse sections. It is the endpoint packing condition here. A bare pullback under a rotation with arbitrary behavior on its countable orbit does not identify ordinary densities from Haar measure. The present interval statement uses explicit arc containments and density-zero fillings.

The [fresh source qualification](candidate_full_source_gate_20261110T2354Z.json) retains the actual rejected GPT candidate and the exact known partial theorem. This owner packet is not an independently accepted proof, a novelty statement, a prize claim or a submission.
