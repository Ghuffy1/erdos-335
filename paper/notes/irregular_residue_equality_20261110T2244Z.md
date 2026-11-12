# Ordinary-density equality with a residue section that has no density

Owner supporting construction for #506, 2026-11-10. For every \(q\ge3\) there are literal positive-integer sets \(A,B\) with
\[
d(A)=1/q,\qquad d(B)=3/(2q),\qquad d(A+B)=5/(2q),\qquad b^*(A+B)=3/q.
\]
Nevertheless \(B\cap(1+2q\mathbb Z)\) and \((A+B)\cap(2+2q\mathbb Z)\) have no ordinary density. Thus existence of all residue densities cannot follow from the full target's hypotheses, even in the strict upper Buck surplus branch.

The period schedule is adapted from Ackelsberg--Richter's Proposition 15.1. Their construction arranges that small shifts are short compared with the local period and the new large shift is a multiple of it. The proof here treats complementary duty cycles on the same schedule, with one large shift per stage and a direct count. [Primary source, Section 15.1](https://arxiv.org/html/2604.12864v1)

## 1. A common sparse set of shifts for two complementary sections

Set \(p_0=1\), and for \(i\ge1\) define
\[
t_i=4p_{i-1}^2,\qquad K_i=t_i^2,\qquad p_i=t_i^5.
\]
Thus \(p_{i-1}\ll t_i\ll K_i\ll p_i\ll K_{i+1}\) in the sense of ratios tending to zero from smaller to larger, and \(p_i\) is a multiple of \(t_i\). In addition \(iK_i/p_i\to0\) and \(iK_{i-1}/K_i\to0\).

Let \(P=\{0,p_1,p_2,\ldots\}\). It has density zero. On the block \([K_i,K_{i+1})\), define D by the residues \(0,\ldots,\theta_i t_i-1\) modulo \(t_i\), where \(\theta_i\) alternates between \(1/4\) and \(3/4\). Let \(E=\mathbb N\setminus D\), with the initial finite block assigned to E. On each large block both D and E are described by a cyclic interval of residues. Both contain intervals of consecutive integers of arbitrarily large length.

We claim that
\[
\overline d((D+P)\setminus D)=\overline d((E+P)\setminus E)=0.
\tag{1}
\]
The same count applies to either set, so let X denote one of them. A periodic cyclic interval of residues modulo t, enlarged by shifts between 0 and \(b<t\), gains at most b residue classes. This follows by moving its right endpoint by b on the circle of residues. An aligned shift divisible by t preserves all its residue classes.

Fix \(K_i\le N<K_{i+1}\). For points of X in the current block, the shifts from P up to \(p_{i-1}\) give at most \(p_{i-1}(N/t_i+1)\) extra elements up to N. Any available shift \(p_i\) is aligned and stays in the current block when its output is at most N. Later shifts are larger than N. This current-block contribution is \(o(N)\), uniformly over the specified N.

If \(N\ge p_i\), the input points in all earlier blocks lie below \(K_i\) and there are at most \(i+1\) available shifts including zero. They contribute at most \((i+1)K_i=o(N)\). If \(N<p_i\), input blocks before \(i-1\) contribute at most \(iK_{i-1}=o(N)\). For the preceding block \(i-1\), the shift \(p_{i-1}\) is aligned inside the block. The other shifts can add at most \(p_{i-2}(K_i/t_{i-1}+1)\) extra points inside it. Outputs across its right endpoint lie in the next \(p_{i-1}\) positions, accounting for all available shifts from that block. Both bounds are \(o(N)\) by \(p_{i-2}/t_{i-1}\to0\) and \(p_{i-1}/K_i\to0\). This proves (1). Since \(0\in P\), both sumsets contain their original sets, so (1) also controls the symmetric differences.

## 2. Combine the two sections without averaging away their oscillation

Put
\[
U=2P,\qquad V=2D\cup(2E-1).
\]
The set V contains exactly one of \(2n-1,2n\) for each \(n\ge1\), so \(d(V)=1/2\) with bounded counting error. By (1),
\[
U+V=2(P+D)\cup(2(P+E)-1),\qquad d((U+V)\triangle V)=0.
\]
Hence \(d(U+V)=1/2\). The set V meets every residue class. For an even modulus use the parity of the desired residue and the corresponding long intervals in D or E. For an odd modulus multiplication by 2 is invertible and either family of long intervals suffices. Since \(0\in U\), \(U+V\) also meets every residue class.

At \(M_i=K_{i+1}-1\), the last block dominates the prefix. Its residue count differs from \(\theta_i(M_i-K_i+1)\) by \(O(t_i)\). The older prefix has length at most \(K_i\). Thus \(|D\cap[1,M_i]|/M_i=\theta_i+o(1)\), with two distinct limit values. The same holds for \(D+P\) by (1).

## 3. Lift to two positive-density summands with a strict surplus

Define
\[
A=q\mathbb N\cup(qU+1),\qquad B=q\mathbb N\cup(qV+1).
\]
These are positive integers, including the contribution from \(0\in U\). The exact output consists of three disjoint residue pieces:
\[
A+B=\{qk:k\ge2\}\ \cup\ \{qk+1:k\ge1\}\ \cup\ \{qw+2:w\in U+V\}.
\]
The residue-one equality follows from the fixed element \(1\in A\) and the full core of B. The density statements follow immediately.

The first two pieces meet every finer residue inside their respective q-classes, and the third does too because \(U+V\) meets every residue class. Their profinite closure is exactly three q-cosets, giving \(b^*(A+B)=3/q\). Both inputs miss residue 2 modulo q. Their difference-gcds are 1 since the core differences include q and the second class differs from a core element by a number congruent to 1 modulo q.

At prefix lengths \(2qM_i+1\), the count ratio in \(B\cap(1+2q\mathbb Z)\) equals \(\theta_i/(2q)+o(1)\). This section comes exactly from the even part \(2D\) of V. At lengths \(2qM_i+2\), the count in \((A+B)\cap(2+2q\mathbb Z)\) has the same two asymptotic ratios, now using \(D+P\). This proves both failures of residue-density existence. A set that is periodic up to density zero has all residue densities, so this sumset is outside the periodic-sumset result as well.

The construction has one rational input density and a sparse exceptional section. It leaves open whether additional restrictions, for example two irrational input densities, force enough regularity for the compact-group argument.

