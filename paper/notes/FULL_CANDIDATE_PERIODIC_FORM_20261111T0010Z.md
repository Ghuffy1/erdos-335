# Erdős 335 full candidate with a periodic-summand alternative

#506 owner synthesis, 2026-11-11. This file states the stronger classification obtained by adding [the macroscopic gluing theorem](periodic_summand_global_gluing_20261111T0007Z.md) to the [original full candidate](FULL_CANDIDATE_20261110T2357Z.md). The original file and all its proof dependencies are preserved. Independent mathematical and scope review remain pending.

## Theorem

Let \(A,B\subset\mathbb N\) have positive ordinary densities \(\alpha,\beta\), and put \(s=\alpha+\beta\). For actual residue supports \(R_q(A),R_q(B)\), define
\[
\gamma=\inf_{q\ge1}\frac{|R_q(A)+R_q(B)|}{q}.
\]
The ordinary equality \(d(A+B)=s\) holds exactly as follows.

1. If \(\gamma=s\), it holds for every such pair. If \(\gamma<s\), it fails.
2. If \(\gamma>s\), it holds precisely for the pairs in at least one of the three classes below.

### Parallel Bohr intervals with finite backgrounds

Choose a modulus h, literal supports \(S=R_h(A)\), \(T=R_h(B)\), and distinguished residues \(i\in S,j\in T\). Every background class on each side is full up to density zero. The residue \(i+j\) has just one expression in \(S+T\), and
\[
|S+T|=|S|+|T|-1.
\tag{1}
\]
After rescaling, the two exceptional sections are literal subsets of parallel closed-arc pullbacks under the same irrational circle rotation. They fill the pullbacks up to density zero. Their arc lengths are positive and sum below 1. The choice \(h=1\) is allowed.

### Two periodic templates with literal sparse sections

There is a modulus q such that \(A\sim_d P_q(S)\) and \(B\sim_d P_q(T)\), where \(P_q(S)\) is the positive integer union of the indicated classes and \(\sim_d\) is symmetric difference of ordinary density zero. Here \(S,T\) are the full background masks, which may be proper subsets of the respective literal supports. Put
\[
W=(R_q(A)+T)\cup(S+R_q(B)).
\]
The finite identity \(|W|=|S|+|T|\) must hold. For each output residue \(w\notin W\), apply the interval test below to all actual exceptional residue pairs \(r\notin S,t\notin T\) with \(r+t=w\bmod q\), rescaling their literal sections and retaining the carry. The packing size must be \(o(N)\) for each w. These exceptional sections individually have density zero, but their literal sums are retained in the test.

### One sparse exceptional section

There is the same finite background and unique-expression template (1) as in the first class. One exceptional section U is nonempty and has ordinary density zero after rescaling. Its partner V has ordinary relative density \(x\in(0,1)\). The roles may be exchanged. Let \(u_0=\min U\) and \(D=U-u_0\subset\mathbb N_0\).

- If U has one element, the pair meets the terminal condition.
- Otherwise let \(g=\gcd(D)>0\). The set V must agree in density with \(V+g\). If U is finite, this is the only further terminal condition.
- If U is infinite, apply the interval test in each residue of V modulo g to the rescaled V section and \(D/g\). Keep only target intervals outside that V section. The packing size must be \(o(N)\) in every residue.

The interval test is explicit in the literal run endpoints. Write each relevant rescaled source section as the disjoint union of its maximal consecutive integer runs. For runs \([a,b]\) and \([c,d]\), their represented block indices form the interval \([a+c+\kappa,b+d+\kappa]\), with the finite carry \(\kappa\) when needed. Clip to the first N indices. In the two-periodic-template class collect all resulting intervals in the given output residue. In the one-sparse-section class intersect them with the complementary runs of the relevant V section. The packing size is the largest sum of integer lengths of a pairwise disjoint subfamily. Singletons and infinite right endpoints are allowed. The family is finite after clipping.

## Proof of necessity

The identity \(\gamma=b^*(A+B)\) follows from literal residue supports. The upper ordinary density is at most \(\gamma\). If \(\gamma=s\) but lower density is less than s, [integer Kneser](https://arxiv.org/html/2602.19014v1) makes the output ultimately periodic and its lower density equal to its Buck density. This contradiction proves the first branch. In particular for \(s=1\) equality is exactly the condition that every residue class at every modulus is met by the output. If \(s>1\), then \(\gamma\le1<s\).

Now assume strict equality, \(d(A+B)=s<\gamma\). Let \(\Delta=\gamma-s\) and let \(\delta_A,\delta_B\) be the upper Buck gaps of the two inputs. The following linked proofs supply the inverse classification.

- [Local deficit compensation](local_deficit_compensation_20261110T2246Z.md) uses actual cyclic windows from Ackelsberg–Richter and a fixed representative in the extra output class. A fixed local modular deficit gives a periodic actual window input.
- [The local dichotomy](common_asymptotic_period_20261110T2349Z.md) gives the first structural class when both \(\delta_A,\delta_B>\Delta\). It iterates the exact Loeb inverse theorem at bounded index, matches the profiles in the two orientations, and then uses the actual all-residue-class integer theorem on the active pair.
- If either own Buck gap is zero, [the 0-or-1 compact model](one_buck_regular_summand_20261110T2342Z.md) gives a periodic-in-density summand. This proof permits arbitrary subsequential residue profiles of the other side.
- If both input gaps are positive and their minimum is at most \(\Delta\), [the finite-frame argument](FULL_CANDIDATE_20261110T2357Z.md) makes one actual input periodic in each local limiting window. [The macroscopic gluing theorem](periodic_summand_global_gluing_20261111T0007Z.md) then makes one actual summand periodic in ordinary density. Its finite labels are determined by the periodic masks and which of their fixed-translate baselines is saturated. Two times of the same label sum to that label by cross-window translate bounds. A positive-measure such label contains a tail by convolution. This yields one label on the rescaled axis and then one ordinary periodic mask by the connectedness of prefix cluster sets.

In either periodic-summand case, use [the exact finite reduction](periodic_summand_exact_reduction_20261110T2330Z.md). If its fixed-translate baseline already has mass s, the output is periodic in density, and [the periodic-output theorem](lemmas_20261110T2218Z.md) forces both inputs periodic in density. Its literal support identity gives the second class and a density-zero escaping sum outside W. If the baseline has smaller mass, finite Kneser coarsens its stabilizer. A fixed literal representative translating the extra active section exhausts the remaining density budget. This produces the unique active expression (1), the third class, and \(V+D\sim_d V\) on the active section. If U has at least two points, each of its fixed translates of V agrees with the output in density. Their differences generate \(g\mathbb Z\), so \(V+g\sim_d V\).

## Proof of the literal tests and of sufficiency

For a finite family of integer intervals, the union length lies between the maximum packing size and three times that size. Greedily choose a longest remaining interval and discard those meeting it. Each discarded interval is in the enlargement of the chosen interval by its length on both ends. The chosen intervals are pairwise disjoint. This proves the factor-three bound. Because the represented intervals come from exact source runs, the packing test is equivalent to zero upper density of the designated escaping integer indices. This does not depend on the existence of any active residue density other than those expressly required.

In the first class, the literal active interval containments and equidistribution give the upper density bound by the sum of arc lengths. The two active sections meet every residue class. Integer Kneser precludes a deficit, so they have that ordinary sum density. Full backgrounds and (1) recombine to s.

In the second class, fixed actual shifts fill W up to density zero. A sum outside W can use only the literal exceptional sections on both sides. The packing test makes their union outside W density zero. The finite identity then gives ordinary output density \(s\).

In the third class, all output classes other than the distinguished one fill from the backgrounds. The active sum differs by a fixed translate from \(V+D\), which contains V. If U has one element this is just V. If U is finite with at least two elements, invariance by g makes every fixed translate by \(D\subset g\mathbb Z\) agree with V in density, and there are finitely many. If U is infinite, the packing test controls the full union of escaping sums in each g-residue. Thus the active output has ordinary relative density x in each case. The finite identity (1) gives ordinary \(d(A+B)=s\).

## Prior scope and literal data

The proof uses [Ackelsberg–Richter](https://arxiv.org/html/2604.12864v1) for intermediate-scale cyclic models and the eventual positive all-residue-class active pair. It uses [Griesmer's exact Loeb inverse theorem](https://arxiv.org/html/1807.01694v3) and [compact inverse theorem](https://arxiv.org/html/1112.6403v3) only after constructing and verifying their respective models. The prior ultimately periodic criterion is credited to the July [White/Claude working report](https://www.erdosproblemaday.com/report/335).

The random even-set example belongs to the numerical branch. The strict degenerate examples can have ordinary residue irregularity in the positive active partner. The literal sparse checks cannot be suppressed merely from density-zero equivalence, as shown by the [digital family](lemmas_20261110T2006Z.md) and the [failure of the unrestricted invariance converse](lemmas_20261110T2218Z.md). These examples account for the limitations of a universal Bohr model without using their failure as a substitute for the classification.
