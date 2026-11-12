# Periodic density in at least one summand in the degenerate branch

Owner addendum to the [full candidate](FULL_CANDIDATE_20261110T2357Z.md), #506, 2026-11-11. This strengthens the common-asymptotic-period conclusion. For any strict equality pair with positive ordinary densities, either the positive Bohr template holds or at least one summand is periodic up to ordinary density zero. The main new argument uses limits of the residue count profiles on the rescaled positive real axis. Independent review is pending.

## 1. Reduction to bounded local periodic templates

Retain \(\alpha,\beta,s,\Delta,\delta_A,\delta_B\) from [the local dichotomy](common_asymptotic_period_20261110T2349Z.md). The case \(\min(\delta_A,\delta_B)=0\) is settled in [the Buck-regular summand proof](one_buck_regular_summand_20261110T2342Z.md). If both input gaps exceed \(\Delta\), the local dichotomy gives the positive Bohr template. Assume henceforth that
\[
0<\min(\delta_A,\delta_B)\le\Delta.
\tag{1}
\]

By the local finite-frame proof in the full candidate, at every common good-window ultralimit at least one actual window input has a periodic 0-or-1 profile. Apply the periodic-input or periodic-output reduction of Section 1 of the local dichotomy. The coarsened moduli in these conclusions are bounded by
\[
D=\left\lceil\max(1/\Delta,1/\delta_A,1/\delta_B)\right\rceil.
\]
Fix \(M\) divisible by every integer from 1 to D. Use relative counts in the M-residues, so a profile is a vector in \([0,1]^M\) whose mean is the corresponding ordinary total. All finite support sets in this proof are literal.

For a periodic A profile with full mask P modulo M, its baseline is \(P+R_M(B)\), of mass \(w_A(P)=|P+R_M(B)|/M\). For a periodic B profile with full mask Q, its baseline is \(R_M(A)+Q\), of mass \(w_B(Q)\). Every such baseline fills in the actual C-window profile by fixed translates and has mass at most s. The mass is independent of further refinement. A full core in a coarse residue contributes every finer residue of each coarse output in its baseline by one literal representative from the other input.

We use three consequences of the finite reductions. They apply equally to a single window sequence or to prefix limits along any subsequence, provided the ordinary totals are \(\alpha,\beta,s\).

1. If \(w_A(P)=s\), then A's periodic mask P determines one unique periodic B profile. In fact the output is the full baseline \(U=P+R_M(B)\), and the positive B support \(T\) satisfies \(R_M(A)+T\subset U\) and \(|T|\ge\beta M\). If this cardinality is larger, the finite completion lemma applied to \(P,T,U\) forces the whole literal output into U, contrary to \(b^*(C)>s\). Thus \(|T|=\beta M\) and B fills T in profile. The same argument applied to the full completion \(\{t:R_M(A)+t\subset U\}\) proves that no other such mask exists. The corresponding assertion holds when \(w_B(Q)=s\).
2. If both input profiles are periodic, at least one baseline has mass s. The proof is the two-periodic-profile baseline argument in the full candidate. If one baseline is smaller, coarsen its stabilizer by finite Kneser to the strict-base case of the periodic-input reduction. The other input has positive mass in each of its actual coarse classes and is periodic at the original fine modulus. A full fine class in each coarse class, together with the literal full carrier of the periodic core on the first side, fills the whole coarse base. One literal sparse shift of the active full fine classes fills the remaining output mass. Hence the opposite baseline has mass s.
3. Suppose the periodic B profile Q has \(w_B(Q)<s\). The strict-base periodic-input reduction gives a modulus \(h\mid M\) with \(h\le1/\delta_B\), a full B background \(T_1\), and \(R_h(B)=T_1\cup\{j\}\), with j the sparse class. The actual \(S=R_h(A)\) has one distinguished class i, the other A classes being full in the target window profile. Put \(x=\alpha-(|S|-1)/h>0\), measured as a fraction of the whole window. The active output class \(u=i+j\) has mass x. Its profile equals that of the A i-section translated by any fixed literal element of the B j-section, since that translated section is contained up to bounded endpoint loss and has the entire mass x. Outside u the output fills its finite baseline and is empty elsewhere. In particular if \(b\in B\) has a fine residue \(t\bmod M\) above j, then for every \(r\bmod M\) above i the target profiles satisfy \(c_{r+t}=a_r\), with the subscript read modulo M. The A, B roles can be swapped.

If both baselines have mass s, the coarsened periodic-output case gives some \(h\mid M\) with \(h\le1/\Delta\). The actual A and B h-supports consist of the full masks plus one literal extra class each. Their extra sum is one residue outside the local full output mask. This follows from aperiodic finite Kneser after coarsening the output stabilizer, as in the local dichotomy.

Consequently an admissible local profile has one of finitely many labels. The label is A together with a periodic mask P with \(w_A(P)<s\), or B together with a periodic mask Q with \(w_B(Q)<s\), or an ordered pair of periodic masks whose baselines both have mass s. These are mutually exclusive by points 1 and 2. Every label prescribes at least one fixed periodic input mask.

## 2. Macroscopic residue profiles

Start with any sequence \(N_k\to\infty\) of prefix lengths. Pass to a rapidly increasing subsequence. For each of A, B, C and each residue r modulo M, extract a further common subsequence on which
\[
F_{E,r,k}(t)=\frac{M}{N_k}|E\cap[1,\lfloor tN_k\rfloor]\cap(r+M\mathbb Z)|
\]
converges uniformly on every compact subinterval of \([0,\infty)\). This follows from boundedness on compacts and the estimate \(0\le F(t')-F(t)\le t'-t+O(M/N_k)\) for \(t'\ge t\), followed by a diagonal extraction on a dense countable set. The limits are nondecreasing 1-Lipschitz functions. Their almost-everywhere derivatives \(a_r(t),b_r(t),c_r(t)\) lie in \([0,1]\). Ordinary total densities give means \(\alpha,\beta,s\) at almost every t. All derivatives vanish in residues outside the corresponding literal support.

Choose a scale \(H_k=o(N_k)\) tending to infinity and dominating the uniform count errors \(N_k\sup|F_{E,r,k}-F_{E,r}|\) on every fixed compact. We also require that it be a common \(U^2\) good scale for A and B along every sequence \((L N_k)\) with positive integer L. This can be done by the nested scale argument. First choose lower scales \(L_k^-=o(N_k)\) dominating the errors on all fixed compact intervals, using a slowly growing compact cutoff and a diagonal choice. Use upper scale \(N_k\). Successively apply [Ackelsberg–Richter, Theorem 8.7](https://arxiv.org/html/2604.12864v1) to A and B on \((L N_k)\) for each L, always using the preceding bounds as the new bounds and taking its subsequence. Choose a diagonal subsequence and an H between the current bounds with all ratios to earlier bounds tending to zero. For each fixed earlier stage, fill in the omitted indices by arbitrary intermediate scales and use Theorem 8.7 followed by restriction to the diagonal. The defining limits of a good scale persist under restriction. This gives the required common choice.

Theorem 9.1 now provides common good starts for the two orientations on \([1,LN_k]\), with \(o(N_k)\) exceptions for each fixed L. The trims and prefix augmentations are those used in the full candidate. Pass to another subsequence so the normalized exceptional counts are summable for each L, by diagonal thinning. For almost every \(t>0\), the starts \(\lfloor tN_k\rfloor\) are then good eventually, by the first Borel--Cantelli lemma applied on each compact interval. At any common Lebesgue point of all the derivatives, the relative count in a window of length \(H_k+o(H_k)\) starting at \(\lfloor tN_k\rfloor+O(H_k)\) tends to the corresponding derivative. Subtract the two uniform count approximations, divide by the window length, and apply the Lebesgue differentiation theorem to intervals of comparable length within distance \(O(H_k/N_k)\) of t. Thus at almost every t the actual local count profile is \((a(t),b(t),c(t))\) and has one of the finite labels from Section 1.

For almost every \(t,u>0\), all three of \(t,u,t+u\) are such Lebesgue points. We have the following cross-window implication for residues r,v modulo M:
\[
a_r(t)>0,\ b_v(u)>0
\quad\Longrightarrow\quad
c_{r+v}(t+u)\ge\max(a_r(t),b_v(u)).
\tag{2}
\]
For the first lower bound choose one actual B element of residue v in the u-window, which exists by its positive count. Its translate of the t-window A section lies in a C window starting within \(O(H_k)\) of \((t+u)N_k\). Pass to the limiting relative count. For the other lower bound choose an actual A element instead. This proof permits the selected literal element to depend on k. It uses uniform macroscopic count approximation for all bounded offsets of size \(O(H_k)\).

## 3. A label is closed under addition of its macroscopic times

We prove that for almost every pair \(t,u\) of the same label, \(t+u\) has that label. The argument only uses the finite profile conditions and (2).

First suppose the target at \(t+u\) has B label Q, with \(w_B(Q)<s\). Use the coarse h, active input classes i,j and active output class from point 3 of Section 1. If the source label at u differs from the target label, the B profile at u must have positive mass in j. Otherwise its literal support \(T_1\cup\{j\}\) and total \(|T_1|/h\) force it to fill \(T_1\) in profile and to have the B mask Q. A mask with this smaller baseline defines the same label. Choose a fine residue \(v\bmod M\) above j with \(b_v(u)>0\).

Since the source labels of t and u agree, at least one of the A profile at t and the B profile at u is periodic at M. If A is periodic, each positive \(a_r(t)\) equals 1. If B is periodic, \(b_v(u)=1\). Thus (2) fills in the target every fine residue \(r+v\) with \(r\) above i and \(a_r(t)>0\). By the actual A h-support S and its total \(\alpha\), the A i-mass at t is at least \(x=\alpha-(|S|-1)/h\). The number of these distinct full fine output classes divided by M is at least that A i-mass. They are all in the target active output class, whose mass is exactly x. Hence all the capacities are attained. The A i-profile at t is a 0-or-1 mask, the other A h-classes are full by total capacity, and the target C active profile fills exactly those fine translates. The target active C profile is the target active A profile shifted by any literal B representative of the fine residue v. Such a representative exists since the source B mass there is positive. It follows that the A profiles at t and \(t+u\) are the same periodic mask P at M.

Both target inputs are now periodic. Since the target B baseline is smaller than s, \(w_A(P)=s\) by point 2 of Section 1. Point 1 makes the B profile at t uniquely equal to Q as well. The source label at t is then the target B label, contrary to the assumption. This proves the assertion for a B-labeled target. The A-labeled target follows by the same argument with the order of the two source times interchanged.

For a target whose two periodic baselines both have mass s, use its coarsened literal supports. Each input has one extra h-class beyond its full mask, and the sum of those extra classes is outside the target output mask. If the A profile at t has no mass in its extra class, capacity forces the target periodic A mask there. That mask has saturated baseline and determines the same periodic B mask by point 1. Hence the source label at t is the target label. Similarly, if the B profile at u has no mass in its extra class, its source label is the target label. If the common source label is different, both extra sections have positive mass. Their sum forces positive target C mass in the forbidden extra output class by (2). This contradiction completes the assertion.

Let \(E_\lambda\subset(0,\infty)\) be the measurable set of times with label \(\lambda\). The preceding assertion says that the convolution of two bounded restrictions of \(1_{E_\lambda}\) is zero almost everywhere off \(E_\lambda\). This follows by the change of variables \((t,u)\mapsto(t,t+u)\) and Fubini. If \(E_\lambda\) has positive measure, choose a bounded positive-measure subset of it. The self-convolution of its indicator is continuous, has positive integral, and is positive on some nontrivial interval \((a,b)\subset(0,\infty)\). Thus \(E_\lambda\) contains that interval up to a null set. Iterating convolution with the same interval gives \((ka,kb)\subset E_\lambda\) up to null sets for all positive integers k. The intervals overlap consecutively for large k and cover a tail. Two different positive-measure labels would therefore both contain a tail, which is impossible. Exactly one label occurs at almost every macroscopic time.

## 4. From the macroscopic label to an ordinary periodic summand

Integrating the macroscopic profiles over \([0,1]\) gives the limits of the actual prefix vectors at \(N_k\). The single macroscopic label guarantees that at least one input vector is its periodic mask, since that mask is fixed throughout the label. If the label is a saturated pair, both are its fixed masks. The other vector can be an average of the remaining variable coordinates of that label.

Let X be the joint cluster set of the actual A and B prefix vectors at M. The preceding extraction starts from any macro sequence, so every point of X belongs to one of the following finitely many closed subsets of X:
- points whose A vector is a prescribed periodic mask P with \(w_A(P)<s\);
- points whose B vector is a prescribed periodic mask Q with \(w_B(Q)<s\);
- singleton pairs of periodic masks whose two baselines both have mass s.

They are disjoint in X. The only possible intersection between different kinds of smaller-baseline slices would have two periodic prefix masks both with smaller baselines. The finite baseline assertion in point 2 applies directly to those prefix limits, since the actual C prefix has ordinary total s and fixed literal translates have bounded endpoint errors. It excludes this intersection. Two different fixed masks on the same side are disjoint, and the saturated pairs have no smaller baseline.

The prefix vectors are bounded, with successive differences tending to zero. A finite disjoint closed cover of their cluster set can have only one nonempty member. Otherwise the nonempty compact members would be separated by a positive distance. Eventually the vectors lie arbitrarily close to their union, and sufficiently small successive steps cannot cross between two of those neighborhoods. This contradicts their being distinct cluster subsets. Hence one periodic mask is fixed in the entire cluster set on at least one side. That input's ordinary residue profile at M is the periodic indicator, proving it agrees in density with the periodic template.

## Consequence for the characterization

For strict equality, the positive Bohr template and the periodic-summand alternative now suffice. The latter has the exact [periodic-summand reduction](periodic_summand_exact_reduction_20261110T2330Z.md). If the output is periodic in density, the [two-periodic-input criterion](lemmas_20261110T2218Z.md) reduces the remaining literal issue to a zero-density sum outside the fixed baseline. Otherwise there is exactly one sparse active section and one positive-density partner. A singleton sparse section is automatic. With two or more literal sparse elements, the positive partner must be invariant in density under their difference-gcd, and the [endpoint packing criterion](FULL_CANDIDATE_20261110T2357Z.md) checks the remaining sparse growth exactly. Thus the interval-run form is still available, but the input structure is stronger than common shift invariance alone.
