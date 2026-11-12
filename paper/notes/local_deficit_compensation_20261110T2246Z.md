# Compensating for a local finite sumset deficit

Owner proof draft for #506, 2026-11-10. This lemma works for arbitrary positive ordinary-density A,B,C=A+B with \(d(C)=s=d(A)+d(B)<b^*(C)\). It does not require individual residue densities. It identifies a constraint on the small finite pairs arising from the intermediate-scale theorem of Ackelsberg--Richter.

## Source inputs and choice of scale

Use Ackelsberg--Richter [Theorems 8.7 and 9.1](https://arxiv.org/html/2604.12864v1). The first three conclusions of Theorem 9.1 require a good \(U^2\) scale for the indicator of A. They do not require B to meet every residue class. The last conclusion, which does require that hypothesis, will be replaced by a direct argument below.

Let \(\alpha=d(A)\), \(\beta=d(B)\). Choose a rapidly increasing sequence \(N_k\) with \(N_{k-1}/N_k\to0\). The maximum of the three prefix count errors for A,B,C up to \(2N_k\) is \(o(N_k)\). Choose \(L_k=o(N_k)\) tending to infinity and dominating that maximum by a factor tending to infinity. Theorem 8.7 gives, after passage to a subsequence, a good scale \(H_k\) with \(L_k\ll H_k\ll N_k\), in the sense that the ratios tend to zero. Take its lower bounding sequence to be \(L_k\) and its upper bounding sequence \(N_k\). Consequently every window \([n,n+Q)\) with \(1\le n\le N_k\) and \(Q=(1+o(1))H_k\) has relative A,B,C counts \(\alpha+o(1),\beta+o(1),s+o(1)\) respectively, uniformly. This is just subtraction of prefix counts.

Theorem 9.1 supplies for almost all \(n\in(N_{k-1},N_k]\) a modulus \(Q_n=(1+o(1))H_k\) and finite \(A_n\subset(A-n)\cap[0,Q_n)\), \(B_n\subset B\cap[1,H_k]\), with counts \((\alpha+o(1))Q_n,(\beta+o(1))Q_n\). The modular sumset agrees with a subset of \((C-n)\cap[0,Q_n)\) except for \(o(Q_n)\) points.

Choose \(D_k\to\infty\) slowly enough that one fixed representative of each actual A or B residue at every modulus \(m\le D_k\) can be chosen among integers up to \(M_k=o(H_k)\). Adjoin all these B representatives to \(B_n\). They lie in \([1,H_k]\) for large k. A modular sum with a newly adjoined representative has an actual sum in the target window unless it wraps, in which case its residue is in \([0,M_k)\). Hence the sumset error remains \(o(Q_n)\). The enlarged \(B_n\) has exactly the literal B residue support at every divisor of \(Q_n\) up to \(D_k\). Its normalized size still tends to \(\beta\).

## Deficit and the extra residue

Let \(C_n=A_n+B_n\) modulo \(Q_n\). Suppose its size has a fixed positive deficit, \(|A_n|+|B_n|-|C_n|\ge\eta Q_n\), for some \(\eta>0\). Finite Kneser gives a stabilizer of index \(h\le1/\eta\), and
\[
|C_n|/Q_n=(|S|+|T|-1)/h,
\]
where \(S=R_h(A_n)\), \(T=R_h(B)\). The latter identity for T uses the adjoined representatives, since \(h\mid Q_n\) and \(h\le D_k\) eventually. Put \(W=S+T\). The modular sumset fills exactly the residue classes in W.

Let \(R=R_h(A)-n\). Then \(R+T\) strictly contains W. Otherwise \(b^*(C)\le |W|/h < s\) for large k. For an extra residue \(u=r+t\notin W\), choose the fixed actual \(a\in A\) with \(a-n\equiv r\bmod h\). The B window \([n-a,n+Q_n-a)\) has \((\beta+o(1))Q_n\) members. Replacing it by the unshifted window changes counts by at most \(2M_k=o(Q_n)\). B is supported on T and every h-class has at most \(Q_n/h\) positions in this window. The t-section thus contributes at least
\[
\left(\beta-\frac{|T|-1}{h}-o(1)\right)Q_n
\]
actual sums in the extra class. These are disjoint from the modular core classes, where at most \(o(Q_n)\) points of the finite sumset were lost. It follows that the actual C-window density is at least
\[
\frac{|S|+|T|-1}{h}+\beta-\frac{|T|-1}{h}-o(1)
=\frac{|S|}{h}+\beta-o(1).
\]
Its density is \(s+o(1)\), whereas the capacity of S gives \(|S|/h\ge\alpha-o(1)\). Hence \(|S|/h=\alpha+o(1)\). For bounded h this eventually forces exact equality. In particular if \(\alpha\) is irrational, no such fixed deficit persists. The modular sumsets then have densities \(s+o(1)\) on the good windows, with the upper bound supplied by Theorem 9.1 and the C-window count. The same argument can be used in the reversed orientation.

## The rational deficit configuration

For a fixed positive deficit and large k, write \(e=s-|W|/h\). We just proved \(\alpha=|S|/h\), so \(e=\beta-(|T|-1)/h\ge\eta-o(1)>0\). Each extra residue of \(R+T\) contributes at least \(e-o(1)\) of the window independently because the residues are disjoint. The C count budget therefore allows exactly one extra residue u.

Since \(|R+T|/h=|W|/h+1/h\ge b^*(C)>s\), we have \(1/h-e\ge b^*(C)-s>0\). Every t that appears in an actual expression \(u=r+t\) has B-window count \(eQ_n+o(Q_n)\): the previous lower bound and the remaining C budget match. Such a t uses all the missing B mass relative to full T classes, namely \(1/h-e\). Consequently t is unique, and so is r.

Finite Kneser also implies \(|R|=|S|+1\). Indeed \(|R+T|=|S|+|T|\) and \(R\) contains \(S\) and the extra r, so the pair \(R,T\) is subcritical by deficit \(|R|-|S|\ge1\). In any stabilizer coset pair that represents u, the number of actual expressions is at least this deficit. To see this, write the finite Kneser formula with stabilizer H and holes \(u_R=|R+H|-|R|\), \(u_T=|T+H|-|T|\). The deficit equals \(|H|-u_R-u_T\). The two representing fibers have sizes at least \(|H|-u_R\) and \(|H|-u_T\), and pigeonhole gives at least their sum minus \(|H|\) complementary pairs. Uniqueness forces deficit one.

Thus in a macroscopic local deficit window, A is nearly full on all but one of its actual h-residues, and B is nearly full on all but the uniquely paired residue. The C window is nearly full on W and has relative count \(e+o(1)\), normalized by the entire window, in the single extra class. The omitted A residue may depend on the window. A proof that these local descriptions produce a global classification is still required.

## Scope and next step

This extends the local lower bound step to arbitrary modular obstructions using actual small representatives and ordinary window counts. The local finite pair can still be near-critical without a fixed deficit. Griesmer's quantitative compact inverse theorem supplies several alternatives for such pairs. A proof must glue their bounded-index descriptions and control any changing large-period component. Ordinary residue-density existence cannot simply be inferred, as the companion irregular-residue construction shows.

