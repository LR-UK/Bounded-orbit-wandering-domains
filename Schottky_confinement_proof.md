# Uniform confinement and local lifting

Fix distinct finite values a,b, a compact set L in the plane, and ε > 0.
There is r in (0,1), depending only on these data, such that every
holomorphic p:D → C omitting a and b with p(0) in L satisfies

\[
p(r\mathbb D)\subset B(p(0),\varepsilon).
\]

There is no assumption that L is disjoint from a or b. Each admissible
central value necessarily omits them, but may approach either one.

## Proof

First take a=0 and b=1 and assume |p(0)|≤R. FunctionTheory's Schottky
estimate gives a finite B=B(R), independent of p, such that |p(z)|≤B
for |z|≤1/2. Thus |p(z)−p(0)|≤B+R there. Schwarz's lemma gives

\[
|p(z)-p(0)|\le 2(B+R)|z|\qquad(|z|<1/2).
\]

Put D=max{2(B+R),1} and r=min{1/4,ε/D}. Then r>0, and |z|<r implies
|p(z)−p(0)|<ε. Compactness of L supplies a common R. For general a,b,
apply this result to q=(p−a)/(b−a), the compact set (L−a)/(b−a), and
ε/|b−a|. Multiplication by |b−a| gives the conclusion for p.

The Lean theorem is
`FunctionTheory.exists_uniform_radius_of_compact_centres_omit_pair`.

## Local lifting

If p also omits E, then p(rD) lies in B(p(0),ε) minus E. Suppose f
restricted to a local source K is a covering over this target, is
holomorphic near K, and is noncritical over the target. Given y in K
with f(y)=p(0), covering-space lifting on the simply connected disc rD
produces h with h(0)=y and f∘h=p. Local inverse branches show that h is
holomorphic, and differentiation gives

\[
h'(z)=\frac{p'(z)}{f'(h(z))}.
\]

The radius was chosen before p, E and this local covering. This order of
quantifiers is explicit in `AreaDeficit.exists_uniform_local_lifting_radius`.
No finiteness assumption on E is needed for this lifting statement.

## Scope

This supplies uniform local confinement without using a hyperbolic metric
on the thrice-punctured sphere. It is an input to the proposed area
argument. It does not construct universal covers of finitely punctured
spheres, prove their hyperbolic area formula, or complete either proposed
dynamical exclusion theorem. The metric convention remains curvature −1.
