# The strict equality classification for two irrational densities

Supporting owner proof for #506, 2026-11-10. This packet removes the ordinary residue-density assumption when both input densities are irrational. It gives a finite modular template and literal Bohr containments for the full strict equality branch in this subcase. Rational input densities and the original all-pairs problem remain open.

## Statement

Let \(A,B\subset\mathbb N\) have positive irrational ordinary densities \(\alpha,\beta\). Write \(C=A+B\), \(s=\alpha+\beta\), and \(b^*(C)=\inf_{m\ge1}|R_m(C)|/m\), where \(R_m\) denotes literal residue support. Then \(d(C)=s\) has the following characterization.

- If \(b^*(C)\le s\), equality holds exactly when \(b^*(C)=s\).
- If \(b^*(C)>s\), equality holds exactly for the following pairs. There is a modulus h, with \(S=R_h(A)\), \(T=R_h(B)\), and active residues \(i\in S\), \(j\in T\). Every A section in \(S\setminus\{i\}\) and every B section in \(T\setminus\{j\}\) fills its residue class up to ordinary density zero. The residue \(i+j\) has just one expression in \(S+T\), and
\[
|S+T|=|S|+|T|-1.
\tag{1}
\]
The two active sections, after rescaling to positive integers, are literal subsets of pullbacks of parallel closed arcs under a common irrational circle rotation. They fill those pullbacks up to density zero. The two arc lengths are positive and sum to less than 1. The case \(h=1\) has no background classes.

The first branch follows from [integer Kneser](https://arxiv.org/html/2602.19014v1) as proved in [the initial reduction](lemmas_20261110T2006Z.md). Below we prove the strict branch. Write \(\Delta=b^*(C)-s>0\).

## 1. Local model and exclusion of periodic output

Assume \(d(C)=s\). Start with any sequence of prefix lengths tending to infinity and pass to a rapidly growing subsequence \(N_k\). Choose a common \(U^2\) good scale \(H_k=o(N_k)\) for \(1_A,1_B\) by the nested applications of Ackelsberg--Richter Theorem 8.7 in [the previous local proof](local_inverse_gluing_20261110T2312Z.md). Set the lower bounding scale above the three ordinary prefix errors for A,B,C up to \(3N_k\). Then all relevant windows of length \((1+o(1))H_k\) have total counts of relative masses \(\alpha+o(1),\beta+o(1),s+o(1)\), uniformly. [Ackelsberg--Richter, Theorems 8.7 and 9.1](https://arxiv.org/html/2604.12864v1)

In the forward orientation, at all but \(o(N_k)\) starts \(n\in[1,N_k]\), Theorem 9.1 supplies \(Q_n=(1+o(1))H_k\), divisible by every fixed modulus eventually, and trimmed sets \(A_n\) from the A window and \(B_n\) from the B prefix. Each trim loses \(o(H_k)\) points. Their cyclic sum lies in the actual C window up to \(o(H_k)\) points. Adjoin to \(B_n\) a slowly increasing literal initial segment of B. The extra wrap errors are \(o(H_k)\). This ensures that \(B_n\) has the full literal B support at every fixed modulus for large k. The reversed orientation has the corresponding assertions with A and B exchanged.

Because the density of the window summand is irrational, [the compensation lemma](local_deficit_compensation_20261110T2246Z.md) rules out any fixed positive modular deficit. Thus the cyclic sums have relative sizes \(s+o(1)\) uniformly on the good windows, and their symmetric differences with the corresponding C windows are \(o(H_k)\). For any sequence of such windows, take an ultraproduct of the finite cyclic groups with Loeb probability measure. The pair and its literal sumset are internal sets of masses \(\alpha,\beta,s\). Every fixed finite-index internal subgroup is represented by the residue subgroup of that index in the finite cyclic groups. We label all window residues by their absolute integer residues, adding the window start back to the A and C coordinates in the forward model.

The whole forward pair cannot have essentially periodic sumset at any finite-index internal subgroup. Here is the argument, which also applies to the reversed pair. If its output fills W modulo h in measure, then \(|W|/h=s\) and \(W=S+T\) for the local A support S and the literal B support \(T=R_h(B)\). Write \(R=R_h(A)\). Let \(T^+\) denote the h-residues of positive B-window mass at the same start, taking the ultralimit. Then \(|T^+|/h\ge\beta\). Fixed translates by actual A representatives show \(R+T^+\subset W\), since the actual C window has zero mass outside W. Also \(S+T\subset W\). Since \(|S|/h\ge\alpha\) is strict by irrationality,
\[
|W|<|S|+|T^+|.
\]
The [finite completion lemma](lemmas_20261110T2218Z.md) applied to \(S,T^+,W\) gives \(R+T\subset W\). This contradicts \(b^*(C)>s\). The capacities and fixed translates concern counts on a fixed residue class, so the \(o(H_k)\) modular approximation error does not affect this argument.

## 2. Iterating the local inverse theorem to a circle interval

Apply [Griesmer, Proposition 10.2 and Corollary 10.4](https://arxiv.org/html/1807.01694v3) to the forward Loeb pair. The same argument will apply in reverse. Type (I) is impossible by Section 1. Type (III) puts the whole pair in two cosets of a finite-index internal subgroup, each filling a parallel Bohr interval in measure. We permit this as a terminal description with no backgrounds.

In type (II), both sets split into full-in-measure background cosets and one nonempty active coset each, with a unique active output expression. If the index is h, S and T are the local supports, \(i,j\) are the active residues, and \(W=S+T\), then (1) holds for this local pair. The rescaled active masses are
\[
x=h\alpha-(|S|-1),\qquad y=h\beta-(|T|-1).
\]
These are irrational and in \((0,1)\). The active sum has relative mass \(z=x+y<1\) by type (II), and every other output coset is full in measure. As \(T\) is the literal B support, every actual B window has relative mass at least \(y-o(1)\) in every class of T. The fixed A translates therefore show \(R_h(A)+T=W\). In particular
\[
\Delta\le |W|/h-s=(1-z)/h,\qquad h<1/\Delta.
\tag{2}
\]
This bound applies to every type (II) description of the whole forward pair. It does not require that its local A support equal the literal A support.

Apply Proposition 10.2 within the active subgroup after translating the two active pieces into it. It is itself the ultraproduct of the corresponding finite cyclic subgroups, with normalized Loeb probability. Its active pair is internal with positive masses and exact equality. Type (I) there would make the whole original local output periodic in measure at the resulting subgroup, because all background output cosets are already full. This was excluded. A further type (II) combines with the outer one by [Griesmer, Lemma 10.14](https://arxiv.org/html/1807.01694v3). Directly, all previous backgrounds remain full at the smaller subgroup, the exceptional expression remains unique, and only the new active output can have a deficit. The new index in the whole group is at least twice the old index. Bound (2) applies to the combined decomposition, so this process is finite. The active masses stay positive and irrational at each step, since they are obtained by multiplying the previous mass by an integer and subtracting the integer number of full background cosets.

It follows that the terminal active pair is type (III), possibly inside a further proper subgroup. Absorb the latter subgroup into the overall modulus h. The old background cosets remain full at this smaller subgroup and the last active input cosets are each single cosets there. The resulting global local profile is still one active coset on each side, with a unique active output expression and (1). When a background is present, bound (2) applies again. When there is no background, the two local inputs and output are in single h-cosets. The same argument with fixed A representatives shows the literal output support at h is that single coset, so (2) again holds with \(z=hs\). Hence the terminal h is bounded by \(1/\Delta\) in every case.

The terminal active pieces fill parallel Bohr intervals in measure in the relevant subgroup. Their active sum agrees in measure with the inverse image of the sum arc. In fact it lies in that inverse image and its mass is the sum of the two arc lengths, which is less than 1 in the normalized active subgroup by type (III). A surjective character to \(\mathbb T\) remains surjective on every finite-index subgroup, since \(\mathbb T\) has no proper finite-index subgroup. The normalized restriction of Loeb probability on each subgroup coset pushes forward to Haar by translation invariance. Consequently each of the three terminal active sections has its same constant relative mass \(x,y,z\) on every fixed finer residue coset. Outside the single active coset, the profiles consist exactly of full or empty residue classes. These statements concern residue counts of the Loeb sets and hence their ultralimits in the integer windows and prefixes.

## 3. Synchronizing the two orientations

Choose a sequence of starts that is good for both forward and reverse constructions. Use the same ultrafilter for the two possibly different finite cyclic moduli. The actual C windows differ in length by \(o(H_k)\), so the two terminal C profiles agree at every fixed modulus. In each description the set of profinite points with relative mass strictly between 0 and 1 is exactly one residue coset. Comparing the two profiles at the least common multiple of their terminal indices shows that the two indices are equal and the two active output residues are equal.

At this common index h, the reverse prefix A support is the entire literal \(R_h(A)\), while the forward local A support is a subset of it. Both have all but one occupied class relatively full and one active class of mass strictly between 0 and 1. Thus their support cardinalities both equal \(\lceil h\alpha\rceil\), so the supports coincide. Likewise the B supports both equal the literal \(R_h(B)\) by \(\lceil h\beta\rceil\). The forward and reverse active expressions of the common output residue are expressions in these same two supports. The uniqueness in (1) forces the same active residue on each input in the two descriptions.

We next arrange uniformity in the window start. Before choosing the first reference starts, pass to a subsequence on which the actual prefix profiles of A and B on \([1,H_k]\) converge at all residue moduli, by a diagonal argument. The reference construction above identifies those limiting profiles as the piecewise constant patterns with one active coset. For every other sequence of common good starts, the forward terminal model has this same B prefix profile on all moduli. Its single partial coset must therefore have the same modulus h and active residue j as the reference. The reverse terminal model similarly has modulus h and A active residue i. Their C profiles agree on all moduli, and the same support cardinality and uniqueness argument forces both local input profiles and the output profile to equal the reference templates.

For each fixed residue modulus this implies uniform convergence of the actual local window counts on the common good starts. Otherwise choose a sequence of starts with a fixed discrepancy, and take an ultrafilter there. The argument just given would identify the same templates and contradict the discrepancy. Averaging the window counts over all starts in \([1,N_k]\) costs \(o(1)\) from the exceptional starts and \(O(H_k/N_k)\) from endpoints. Thus along this prefix subsequence, the actual A, B, and C residue profiles converge at every modulus to the terminal templates.

## 4. One template on all prefixes

The preceding argument starts from an arbitrary sequence of prefix lengths and yields a subsequence with a template of bounded h. There are only finitely many such templates because \(h<1/\Delta\), the supports and active residues are finite choices, and \(x,y,z\) are determined by h, the support sizes, and \(\alpha,\beta\). Take M divisible by all positive integers below \(1/\Delta\). At modulus M the joint vectors of normalized A, B, and C prefix counts are bounded and have successive differences tending to zero. Every subsequential cluster point is one of the finitely many template vectors. A bounded sequence in finite-dimensional Euclidean space with successive differences tending to zero and finite cluster set has exactly one cluster point. Indeed, if there were two, choose disjoint small balls about the finitely many points with positive separations. All sufficiently late terms lie in their union, and sufficiently small steps cannot move between balls. This proves convergence at M.

The single partial coset of the A template is visible at M, so h and i are uniquely determined from this vector. The full and empty classes and the B active class are also determined. Thus every template subsequence at any higher or unrelated modulus uses this same template. The subsequence argument gives ordinary convergence at every modulus. In particular the active sections each have their positive relative densities x and y in every fixed refinement, and hence meet every residue class after rescaling. Their literal sum is the unique active output section by (1) and has ordinary relative density \(z=x+y<1\). Apply [Ackelsberg--Richter, Theorem 1.4](https://arxiv.org/html/2604.12864v1) to the rescaled pair. Its internal modulus is 1 because both active sets meet every residue class, and a zero-density degenerate case is excluded. This gives the literal Bohr interval containments and density-zero fillings stated above.

For sufficiency, the terminal Bohr pair has ordinary sumset density equal to its two arc lengths by equidistribution and the integer Kneser lower bound, since both input pullback fillings meet every residue class. In each background output residue a single fixed element from one side translates a full-in-density class from the other. The unique active expression and (1) then give exactly \(d(A+B)=d(A)+d(B)\).

## Scope and attribution

The intermediate-scale cyclic modeling is borrowed from Ackelsberg--Richter and the exact Loeb inverse theorem and combination lemma from Griesmer. The additional arguments are the exclusion of periodic local output using literal representatives, the bound on the iteration index from the global Buck gap, the synchronization of the two profiles, and the connectedness argument for prefix limits. No full claim for arbitrary rational or irregular inputs is made. In particular the strict irregular example in [the separate construction](irregular_residue_equality_20261110T2244Z.md) has a rational input density and a sparse active piece, and is compatible with this theorem.
