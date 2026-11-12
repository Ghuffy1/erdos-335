# Exact reduction when a summand is periodic in density

Supporting owner proof for #506, 2026-11-10. Suppose \(A,B\subset\mathbb N\) have positive ordinary densities \(\alpha,\beta\), \(d(A+B)=s=\alpha+\beta\), and \(b^*(A+B)>s\). Assume that B agrees in density with a union of residue classes. This argument needs no residue-density hypothesis on A.

Choose a period q and nonempty \(T\subset\mathbb Z/q\) such that B agrees in density with \(P_q(T)\). Thus \(\beta=|T|/q\). Write \(R=R_q(A)\), \(W=R+T\). The part of B in \(P_q(T)\) fills each class there in ordinary relative density. For each \(w\in W\), one actual A element and a full B section translate to fill w in the sumset. Consequently \(s\ge |W|/q\).

If \(s=|W|/q\), the output is periodic in density with template \(W\). The [periodic-output theorem](lemmas_20261110T2218Z.md) then makes A periodic in density as well, and its exact two-periodic-input criterion applies. This branch is impossible for irrational \(\alpha\).

Suppose \(s>|W|/q\). Since \(\alpha\le |R|/q\), this gives \(|W|<|R|+|T|\). Let L be the stabilizer of W in \(\mathbb Z/q\), and let \(h=q/|L|\). Write \(S=R_h(A)\), \(T_1\) for the projection of T mod h, and \(W_1=S+T_1\). The quotient \(W_1\) has trivial stabilizer and finite Kneser gives
\[
|W_1|=|S|+|T_1|-1.
\]
The actual output fills all classes in \(W_1\), and \(\beta\le |T_1|/h\).

There is a literal extra output residue \(u=r+t\notin W_1\), with \(r\in S\) and \(t\in R_h(B)\). Otherwise \(b^*(A+B)\le |W_1|/h<s\). In fact \(t\notin T_1\). Choose a fixed literal B element in class t. Its translate of the A r-section has lower density at least
\[
x=\alpha-(|S|-1)/h.
\]
Here \(x>0\), because \(s>|W_1|/h\) and \(\beta\le|T_1|/h\). Counting the disjoint base classes and this translate gives
\[
s\ \ge\ \frac{|W_1|}{h}+x
=\alpha+\frac{|T_1|}{h}
\ \ge\ \alpha+\beta=s.
\]
Hence \(\beta=|T_1|/h\), and the B classes in \(T_1\) are relatively full in density. To see fullness directly, the original periodic template of B lies in \(P_h(T_1)\), has the same density as that larger template, and both templates are periodic. Their difference has density zero. The remaining B classes have density zero.

The actual C u-section has density x by subtracting the full base from the ordinary total and using the lower bound x there. The actual A r-section has density x by its translate into u and its capacity lower bound. All other A classes are relatively full. Any second extra output class would have lower density at least x by another fixed B translate, exceeding the remaining budget. Therefore the actual \(R_h(C)=W_1\cup\{u\}\). Strict upper Buck surplus gives \(0<x<1/h\). If another representation of u used an A class different from r, that full A section would force the C u-section full, a contradiction. Hence u has a unique expression \((r,t)\) in the actual supports.

Every literal B residue \(t'\notin T_1\) contributes some extra output residue. Otherwise \(S+(T_1\cup\{t'\})=W_1\). The quotient sumset is aperiodic, so finite Kneser would give \(|W_1|\ge|S|+|T_1|\), contradicting the displayed identity. Uniqueness of the extra output and its expression therefore gives \(R_h(B)=T_1\cup\{t\}\). We have obtained the exact finite quasi-periodic data with one positive active A section and one nonempty sparse B section. The finite identity for the actual supports is
\[
|R_h(C)|=|R_h(A)|+|R_h(B)|-1.
\]

Conversely, for any literal pair admitting these finite data, every nonactive output class is relatively full by fixed translates. Its only remaining output is the sum of the two actual active sections, rescaled to integers with a possible fixed carry. The required equality is therefore exactly the assertion that the sparse active B section U does not increase the density of its positive-density partner V. Equivalently, choose \(u_0\in U\) and translate both the sparse set and output to make \(0\in U-u_0\). The set \((V+(U-u_0))\setminus V\) must have upper density zero. This condition explicitly retains the literal sparse section.

If U is finite and has at least two points, this condition is equivalent to \(V+g\) and V agreeing in density, where \(g=\gcd(U-U)>0\). Necessity follows since all translates \(V+u\) are contained in the sum and have its full density, so their pairwise differences have density zero. The shifts preserving V up to density zero form a subgroup of \(\mathbb Z\), which then contains g. For sufficiency, each of the finitely many translates differs from a fixed one by a density-zero set, and a finite union retains this property. For a singleton U it is automatic. For infinite U, finite-shift invariance is necessary but can fail to control the whole union, as in [the squares counterexample](lemmas_20261110T2218Z.md).

This gives an exact reduction to a sparse terminal for every strict equality pair with one periodic-in-density input and nonperiodic-in-density output. It does not classify all infinite sparse non-growth pairs.
