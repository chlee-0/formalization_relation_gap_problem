# Formalization of a Relation Gap in Lean 4

This repository contains a Lean 4 formalization, using Mathlib, of a **relation gap** and **global deficiency zero** for the group in OpenAI's *A Counterexample to Wall's D(2) Problem* (October 6, 2026). The Lean formalization was carried out primarily by AI models, Claude Opus 5.5 and GPT-6.1 Sol.

## Scope

**OpenAI's original contribution.** In *A Counterexample to Wall's D(2) Problem* (October 6, 2026), OpenAI constructs the group $G$ and proves a counterexample to Wall's D(2) problem. The group construction, perfect normal subgroup, commutator identities, character, Fox calculations, and torsion obstruction used here originate in that work. The [original preprint (commit `adc7f124`)](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026) does not include a Lean formalization.

**Results established here.** Building on OpenAI's construction, we prove a relation gap for the specified epimorphism $F\twoheadrightarrow G$ and establish that $G$ has global deficiency zero. Neither result is explicitly stated in the original preprint.

**Scope of the formalization.** The Lean development proves the required obstruction using a combinatorial chain model, without assuming it as an additional axiom. **It does not formalize OpenAI's complete geometric/topological proof of the D(2) counterexample.**

## Main results

Let $F$ be the free group on $x_1,a_1,x_2,a_2,s$ and let

$$
G=\langle x_1,a_1,x_2,a_2,s\mid
x_1a_1x_1^{-1}=a_1^4,\quad x_2a_2x_2^{-1}=a_2^3,\quad
x_1=a_2^{13},\quad sx_2s^{-1}=a_1^5,\quad x_2^3=1\rangle.
$$

Write $q:F\twoheadrightarrow G$ for this **specific quotient map** and $N=\ker q$. The relation-gap statement concerns this fixed epimorphism; the deficiency statement concerns all finite presentations of $G$.

**Relation gap.** The relation module $N_{\mathrm{ab}}=N/[N,N]$, with its
canonical $\mathbb ZG$-action induced by conjugation, is generated as a
$\mathbb ZG$-module by four elements but no fewer. In contrast, $N$ is the normal closure in $F$ of five elements, but no set of fewer than five elements normally generates $N$:

$$
d_{\mathbb ZG}(N_{\mathrm{ab}})=4<5=d_F(N).
$$

**Global deficiency zero.** Every finite presentation of $G$ with $m$ generators and $k$ relators satisfies $m\leq k$, and a five-generator, five-relator presentation exists. Thus

$$
\delta(G)=0.
$$

## Where to start

Start with [Statements.lean](Statements.lean) for the precise theorem statements. The underlying proofs are in [FoxFilling.lean](D2RelationGap/FoxFilling.lean) and [DeficiencyZero.lean](D2RelationGap/DeficiencyZero.lean).

## Attribution

**OpenAI (2026).** *A Counterexample to Wall's D(2) Problem*. OpenAI Math Release preprint. [Paper (PDF)](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/wall-d2-counterexample.pdf) · [Preprint directory](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026).
