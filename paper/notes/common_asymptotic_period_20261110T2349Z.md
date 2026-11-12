# Positive Bohr templates and common asymptotic periods

Supporting owner proof for #506, 2026-11-10. Let \(A,B\subset\mathbb N\) have positive ordinary densities \(\alpha,\beta\), and let \(C=A+B\) have \(d(C)=s=\alpha+\beta<b^*(C)\). Define the three literal Buck gaps
\[
\Delta=b^*(C)-s,\qquad \delta_A=b^*(A)-\alpha,\qquad \delta_B=b^*(B)-\beta.
\]
This packet applies to rational as well as irrational densities.

1. If \(\delta_A>\Delta\) and \(\delta_B>\Delta\), there is one exact positive Bohr template, with all the finite support conditions and literal terminal containments in [the irrational-density classification](irrational_input_classification_20261110T2322Z.md).
2. If \(0<\min(\delta_A,\delta_B)\le\Delta\), there is a positive integer M such that \(A+M\) and A, \(B+M\) and B, and \(C+M\) and C agree in ordinary density. Thus the exact residue masks of each of these sets in consecutive blocks of length M change at only \(o(N)\) of the first N block boundaries.
3. If either input Buck gap is zero, [the Buck-regular summand theorem](one_buck_regular_summand_20261110T2342Z.md) gives one summand periodic in density. Its further exact finite reduction is [here](periodic_summand_exact_reduction_20261110T2330Z.md).

Item 2 is a necessary structural theorem. An exact description of all permitted interactions between the changing masks remains unresolved.

## 1. Local periodic input and output

Fix a common good-window sequence from [the modulated-sum construction](irrational_input_classification_20261110T2322Z.md), with an ultrafilter if needed. All actual windows have total relative masses \(\alpha,\beta,s\), and every fixed literal shift changes the endpoint counts by \(o(1)\). A local input or output will be called periodic at q if on each q-class its actual window fills the class in the limit or has zero mass. This is equivalent to agreement in the normalized window metric with the stated finite periodic template. In particular the template is an assertion about actual membership counts on that window, not only about its abstract literal support.

Suppose first that the actual B window is periodic at q, with full-class mask T. Repeat [the periodic-summand reduction](periodic_summand_exact_reduction_20261110T2330Z.md) in the local windows, with actual supports \(R=R_q(A)\), \(R_q(B)\). Every fixed literal A representative translates the full B-window section into a full output section. Hence the base \(W=R+T\) is full in the C window and \(s\ge |W|/q\).

If \(s>|W|/q\), the finite Kneser and extra-residue argument of that reduction applies with exactly the same inequalities to window counts. For completeness, coarsen by the stabilizer of W to modulus h, put \(S=R_h(A)\) and \(T_1\) the projected B mask, and get an aperiodic base \(W_1=S+T_1\) of size \(|S|+|T_1|-1\). An actual extra residue \(u=r+t\notin W_1\) exists by \(b^*(C)>s\). Its fixed literal B translate of the actual A window has relative mass at least \(x=\alpha-(|S|-1)/h>0\), measured as a fraction of the whole window. Thus \(s\ge |W_1|/h+x=\alpha+|T_1|/h\ge s\), and all are equalities. B is locally full on \(T_1\), its literal support is \(T_1\cup\{t\}\), and A is locally full on \(S\setminus\{r\}\) with active mass x. The extra output is only u and has the unique expression \((r,t)\). Uniqueness and the absence of further literal B residues follow from the same capacity and aperiodic finite Kneser arguments as in the periodic-summand proof.

At this modulus the literal A closure outside its active class consists of the full background cosets. The literal C closure outside u consists of its full base cosets. The active C closure contains a translate of the active A closure, by one fixed actual B element in t. Subtracting the corresponding ordinary window masses gives
\[
\delta_A\le\Delta .
\tag{1}
\]
Also \(\delta_B\le1/h\). If \(\delta_B>0\), the literal active B section contains at least two points. Let g be the positive gcd of its differences after rescaling by h. For every fixed literal B element in t, its translate of the active A window fills the active C window in measure, since both masses are x. Thus the active A window and active C window are invariant in measure under translation by \(hg\). Together with the full backgrounds, the whole local A and C windows have this invariance. The B window is periodic at h.

If instead \(s=|W|/q\), the C window is periodic at q. More generally, if an actual C window is periodic at any fixed q, write U for its full mask and P,Q for the positive-mass q-supports of the actual A and B windows. Fixed literal translates give
\[
(P+R_q(B))\cup(R_q(A)+Q)\subset U .
\]
Capacity gives \(|P|+|Q|\ge sq=|U|\). A strict inequality contradicts the finite completion lemma, which would then give \(R_q(A)+R_q(B)\subset U\) and hence \(b^*(C)\le s\). Thus both inputs are locally full on their respective masks P,Q. The same completion argument shows that the displayed union equals U, since a smaller union also has size below \(|P|+|Q|\).

If one of the two sets in this union is strictly smaller than U, the strict periodic-input case just proved applies in the corresponding orientation. In the remaining case both sets equal U. The masks P,Q are the full finite completions of the opposite literal supports inside U. For instance, let \(P^*=\{r:r+R_q(B)\subset U\}\). If \(P^*\supsetneq P\), apply the finite completion lemma to \(P^*,Q,U\), using \(R_q(A)+Q\subset U\) and \(P^*+R_q(B)\subset U\). This forces the whole literal output inside U, again impossible. Thus \(P=P^*\), and similarly for Q.

Coarsen by the stabilizer of U. The full completions are invariant under it, so both local inputs and the output are periodic at the resulting modulus h. The projected U is aperiodic and the finite identity \(|U|=|P|+|Q|\) holds there, using the new quotient notation. Since \(P+R_h(B)=R_h(A)+Q=U\), aperiodic finite Kneser implies that each literal input support has at most one extra residue beyond its full mask. Each must have an extra, since otherwise the whole literal output would be inside U. The only output beyond U is their sum. Its literal carrier is the sum of the two extra carriers, so each of their masses \(\delta_A,\delta_B\) is at most its mass \(\Delta\). Also \(h\le1/\Delta\). This proves both the gap assertion and the bounded-period reduction for local periodic output.

In particular, any local periodic input or output implies
\[
\min(\delta_A,\delta_B)\le\Delta.
\tag{2}
\]
If both input gaps are positive, the same proof gives a bounded set of possible invariance shifts for both inputs and the output in every such window. They are moduli \(h\le1/\Delta\), or products \(hg\) from the literal extra section of the periodic input at some \(h\le1/\delta_A\) or \(h\le1/\delta_B\).

## 2. Other local alternatives

Use the same cyclic models and bounded-size removals as in [the irrational-density proof](irrational_input_classification_20261110T2322Z.md), but with arbitrary densities. Choose the common scale as in that proof. Each orientation either has a positive modular deficit in the ultralimit or is an exact critical Loeb pair. In the deficit case [local compensation](local_deficit_compensation_20261110T2246Z.md) makes the window summand locally periodic at the finite stabilizer index, so Section 1 applies.

For an exact critical Loeb pair, an essentially periodic output in Griesmer's Proposition 10.2 makes the actual C window periodic by the \(o(1)\) approximation. Section 1 again applies. The other alternatives can be iterated through quasi-periodic active sections, as in the irrational-density proof. At every quasi-periodic description of the whole local pair at index h, the prefix input has its entire literal h-support, fills all but one class, and has at most \(1/h\) excess of literal Buck density over ordinary density. If the prefix input has positive Buck gap, h is bounded by its reciprocal. Thus iteration stops after finitely many steps, either with a positive terminal relative Bohr interval pair, a periodic output, or a zero-mass active input. The same bound applies if a further subgroup from the positive interval alternative is absorbed into the full quasi-periodic description. If no background is present the interval pair simply lies in a single class on each side.

For a positive terminal with local A support S, literal prefix B support T, active relative masses \(x,y>0\), and \(W=S+T\), \(u=i+j\), the C window fills W outside u and has constant relative density \(z=x+y<1\) on every fixed refinement of u. These facts follow from the surjective interval character and exact equality, as in the irrational-density proof. The actual B window has positive relative mass in every T-class by capacity, so fixed literal A translates imply \(R_h(A)+T=W\). Each finer residue inside W is literally met by C because of the positive local counts. Hence its literal carrier is precisely the union of W cosets, and \(\Delta=(1-x-y)/h\). The same positive refinements for the local A and prefix B imply
\[
\delta_A\ge(1-x)/h>\Delta,\qquad \delta_B=(1-y)/h>\Delta.
\tag{3}
\]
The same conclusions hold with no backgrounds.

If a zero terminal is on the window side, that actual window input is periodic in measure, so Section 1 applies. If the prefix side is zero and the window side positive, the local output consists of full backgrounds and the active output of equal mass to its positive window summand. Every fixed literal element of the zero prefix section occurs in the local model, because we augmented each prefix by a slowly increasing literal initial segment. Thus the same invariance under \(hg\) holds for the whole window summand and output, with g the positive gcd of differences of the literal zero section after rescaling. The section has at least two elements when the prefix Buck gap is positive. The index bound is again \(h\le1/\delta_{\rm prefix}\). These alternatives use [Griesmer, Proposition 10.2, Corollary 10.4, and Lemma 10.14](https://arxiv.org/html/1807.01694v3).

## 3. Two orientations when the gaps are large

Suppose \(\delta_A,\delta_B>\Delta\). Section 1 rules out a periodic actual window input or output. Section 2 then rules out every fixed local modular deficit and every zero window terminal. At any common good-window limit, the two orientations are therefore positive terminal or zero prefix terminal.

Both orientations cannot have zero prefix terminals. Their actual prefix profiles on the same \([1,H_k]\) would each be periodic in measure at fixed moduli, with the same ordinary totals. Those prefixes are common windows for purposes of the fixed-translate argument of Section 1. The actual C prefixes \([1,H_k]\) have ordinary total s, and fixed shifts by literal elements preserve their normalized counts up to \(o(1)\). A local periodic input at these prefixes therefore contradicts (2). At least one orientation has a positive terminal.

We show the other orientation cannot be a zero prefix terminal. Name its window input X, prefix input Y, and terminal modulus k. Write S for the local X support, \(T=T_1\cup\{j\}\) for the literal Y support, \(i,j\) for its active residues, \(W=S+T\), \(u=i+j\), and \(x>0\) for the relative active X mass. The Y prefix fills \(T_1\) and has zero active mass, so its total relative mass at k is \(|T|-1\). The C window is full on \(W\setminus\{u\}\) and empty outside W, with relative mass x in u. The opposite positive terminal gives one partial output class \(u'\bmod h\) with constant relative density strictly between 0 and 1 on every refinement. This class lies inside u, so \(k\mid h\). In the positive orientation X is the prefix input, with full literal support at h and positive active mass. Capacity therefore gives the actual X window positive mass in every literal X h-class.

Put \(R=R_k(X)\supset S\). If \(R+T\) extends outside W, fixed literal X translates force the actual Y window to have zero mass in a T-class and to fill all the others by capacity. This makes it periodic and is impossible by (2). Hence \(R+T=W\). If \(R\supsetneq S\), the finite Kneser hole formula gives at least two expressions of each element of W. In particular u has one with a Y residue in \(T_1\). Lift that expression to \(u'\bmod h\) by a fixed literal X representative. The corresponding Y prefix h-section is full and the X window h-section has positive mass by the preceding capacity observation. Their forward modular sum fills \(u'\) in measure, contrary to its partial profile. Thus \(R=S\).

The actual X i-section then has relative mass at least \(x-o(1)\) in both its prefix and its window. The actual Y window has positive mass in j, since otherwise it is periodic by capacity. Their opposite-orientation modular active sum therefore has a fixed deficit against the relative C u-cap x. Finite Kneser gives a periodic core at some bounded further index d, of relative capacity at most x, with the entire literal X i-support at d on the prefix side. If the core capacity equals x, the actual C u-profile is periodic at kd because the core is contained in it in measure and has its entire mass. This contradicts the partial \(u'\bmod h\) profile, by taking a common refinement. Thus the core capacity is strictly below x. The literal active pair has upper Buck capacity at least x by the lower X i-capacity and one fixed Y j-element. There is an extra residue outside the core. Translating the actual X i-window by a fixed literal Y element in a representing class gives exactly the compensation inequality from the local deficit proof. If the local Y active support in that quotient is \(S_2\), the relative C u-mass is at least \(x+|S_2|/d>x\). This contradiction excludes the zero terminal.

Both local orientations are therefore positive. Their matching actual C profile identifies the same h and active output. Positive active masses and support capacities identify the literal supports on both sides, and uniqueness fixes the two active residues. Diagonalize the actual prefix profiles at all moduli as in the irrational-density proof. Each positive template is then uniform on all good starts of the selected macro subsequence. The terminal indices are bounded by \(1/\Delta\) from (3), and the ordinary profile cluster set at a common multiple of these moduli is finite. Vanishing successive prefix increments fix one template globally. The active sections have all ordinary residue densities and meet every residue class after rescaling. [Ackelsberg--Richter, Theorem 1.4](https://arxiv.org/html/2604.12864v1) now gives the actual literal parallel Bohr interval containments, with the same sufficiency proof as before. This proves item 1.

## 4. Common asymptotic periods when both input gaps are positive

Assume \(0<\min(\delta_A,\delta_B)\le\Delta\). Equation (3) rules out every positive local terminal in either orientation. Take
\[
D=\left\lceil\max\{1/\Delta,1/\delta_A,1/\delta_B\}\right\rceil.
\]
For each h from 1 to D and each literal h-section of either input with at least two points, record \(hg\), where g is its rescaled difference-gcd. Let M be a common multiple of these finitely many positive integers and of all h from 1 to D.

At every common good-window ultralimit, the alternatives in Sections 1 and 2 give invariance in measure under M for the actual window inputs and output. A periodic input, periodic output, or fixed deficit uses Section 1. A zero window terminal is periodic and uses the same argument. A zero prefix terminal gives the recorded shift for the window input and output, and the opposite orientation does the same for the other input unless Section 1 already covers it. All comparisons are on actual windows with lengths \(H_k+o(H_k)\). At any fixed integer shift, the cyclic endpoint discrepancies are \(o(H_k)\), so the invariance statement gives the actual local symmetric-difference counts.

If any of these normalized counts failed to tend to zero uniformly on the common good starts, choose a discrepant start sequence and an ultrafilter. The preceding alternatives give invariance there, a contradiction. Average the window counts over starts to obtain zero limiting prefix density of the shift discrepancies along a subsequence of any prescribed macro prefix sequence. Therefore the full ordinary discrepancy densities are zero. In blocks of length M, the number of mask changes up to block index N is bounded by the sum of the M residue-by-residue discrepancy counts, which is \(o(N)\). This proves item 2.

The argument uses actual fixed shifts even in the finite periodic reductions. A local full mask does not discard literal sparse elements in other residue classes. These elements account for the distinction between the literal Buck gaps and the window masses throughout the proof.
