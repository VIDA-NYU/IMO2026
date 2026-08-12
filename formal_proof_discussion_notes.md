# From Informal Proofs to Human-Readable Formal Mathematics

## Context

This repository contains informal Markdown proofs and fully verified Lean 4
formalizations for six IMO-style problems. The informal proofs were generated
and revised by Meta's Muse Spark through interactions with the repository
author, with [GPT-5.6](https://developers.openai.com/api/docs/guides/latest-model)
used as a judge of the drafts. They were then reviewed for
mathematical correctness and compared with the Lean proofs. These notes also
discuss what the reported AxiomProver runtimes mean.

The broader question is how to retain the certainty of formal verification
while presenting proofs in a form that mathematicians can read, discuss, and
learn from.

## Provenance and methodology

The artifacts in this repository were produced by several distinct actors and
checking mechanisms:

| Artifact or role | Producer or checker | Function in this exploration |
|---|---|---|
| Formal Lean solutions | AxiomProver | Discovered and constructed the checked Lean proofs |
| Informal Markdown proofs | Muse Spark, interacting with the author | Generated and revised the human-readable arguments |
| Human guidance | Repository author | Prompted the process, questioned results, supplied feedback, and requested revisions |
| Model-based judging | GPT-5.6 | Reviewed the informal drafts and identified issues for further revision |
| Mechanical verification | Lean/AXLE | Checked the final formal proof obligations |

The current informal proofs should therefore be described as
**human-in-the-loop, model-generated proofs**, not as unaided human solutions.
Their production was iterative: Muse Spark produced explanations, the author
interacted with and challenged them, GPT-5.6 supplied a separate model judgment,
and the drafts were revised and checked for correspondence with the Lean
development.

The GPT-5.6 judgment and the Lean check play fundamentally different roles. A
model judge can assess clarity, plausibility, completeness, and correspondence
at the level of mathematical exposition, and can find issues worth
investigating. Its verdict remains fallible. Lean checks a precise theorem
mechanically, but does not judge whether the prose faithfully explains that
theorem or whether the formal statement faithfully represents the original
problem. The two forms of review are complementary rather than interchangeable.

This provenance limits the conclusions that can be drawn from a direct cost
comparison. The informal and formal proofs were produced by different systems,
under different interaction patterns, and the polished informal proofs benefited
from model judging and comparison with an already verified formal artifact.
They are evidence about an effective mixed workflow, but not a controlled
measure of “AI informal proof cost versus AI formal proof cost,” and still less
of “human proof cost versus formal proof cost.”

For reproducibility, future runs should retain the interaction transcripts,
initial and revised drafts, judge prompts and verdicts, exact model and harness
versions, reasoning settings, human interventions, and the Lean declarations
used for comparison. Because a model-family name may refer to multiple variants
or a moving alias, recording only “GPT-5.6” or “Muse Spark” may be insufficient
for an exact replication.

## 1. Correctness and fidelity of the informal proofs

The informal proofs were revised several times after gaps and misleading
shortcuts were identified. In their current form, they capture the essential
mathematical arguments of the formal proofs.

The correspondence is especially close for Q1, Q2, Q4, Q5, and Q6:

- **Q1:** invariance of the gcd of the prime valuations, followed by a
  decreasing termination measure and reconstruction of the terminal value.
- **Q2:** coordinates, conversion of the three angle hypotheses into polynomial
  identities, and a final algebraic certificate implying that the circumcenter
  lies on the perpendicular bisector of the relevant segment.
- **Q4:** induction for angles that are positive multiples of the target angle,
  an integer-interval lemma, and a safe-triangle obstruction in the converse
  direction.
- **Q5:** an orbit identity for the function, nonnegativity of its displacement,
  comparison of different positive-displacement orbits, and a connectedness
  argument excluding a mixture of fixed and translated points.
- **Q6:** stabilization of the relevant finite family of small-prime supports,
  periodicity of the resulting goodness predicate, a residue pigeonhole
  argument, and a backward minimality argument upgrading eventual periodicity
  to pure periodicity.

Q3 needs a small qualification. Its informal and formal proofs establish the
same main intermediate statements, and the upper-bound construction is closely
aligned. However, the formal lower-bound kernel uses a more specific argument
than an elementary dyadic induction:

1. Descendant pieces are labelled by their original dyadic gap.
2. Sorted pieces are paired adjacently, turning their alternating sum into a
   pairing defect.
3. The pairing defines a graph on the original labels.
4. Since the graph has fewer edges than vertices, it has a nontrivial signed
   component coloring.
5. The associated signed sum of powers of two has absolute value at least one.
6. That signed sum is bounded by the pairing defect, proving the desired lower
   bound.

This example illustrates an important requirement for informal summaries: they
should describe the proof that was actually formalized, rather than silently
substituting a plausible alternative proof.

## 2. Size overhead of exact Lean formalization

The standalone `solution.lean` files already include their definitions and
theorem statements, so they can be compared directly with the informal
Markdown files. The separate `problem.lean` files are not included below,
because counting them would duplicate the formal statements.

| Problem | Informal lines | Lean lines | Line overhead | Lean declarations | Argument correspondence |
|---|---:|---:|---:|---:|---|
| Q1 | 136 | 521 | 3.8x | 38 | Same |
| Q2 | 219 | 1,224 | 5.6x | 19 | Same |
| Q3 | 210 | 4,229 | 20.1x | 144 | Same upper proof; more specific formal lower kernel |
| Q4 | 171 | 520 | 3.0x | 18 | Same |
| Q5 | 145 | 457 | 3.2x | 12 | Same |
| Q6 | 189 | 771 | 4.1x | 33 | Same |
| **Total** | **1,070** | **7,722** | **7.2x** | **264** | |

Across all six problems, the Lean sources are also approximately 8.4 times
larger in bytes and 9.7 times larger in nonblank lines.

These ratios should not be interpreted as a universal constant. They depend on
the choice of representations, the available Mathlib API, the level of detail
in the informal proof, the amount of commentary in the Lean code, and how much
work is compressed by tactics such as `ring`, `nlinarith`, and `omega`.

The largest sources of overhead are:

- proving positivity and nonzeroness conditions;
- converting between natural numbers, integers, and real numbers;
- transporting statements through lists, multisets, finite sets, sorting, and
  permutations;
- verifying index and cardinality bounds;
- connecting an abstract combinatorial construction back to the objects in the
  original problem;
- making induction and well-foundedness explicit;
- supplying library lemmas that are routine on paper but not already available
  in the required form.

Q3 is the outlier because it requires extensive infrastructure for labelled
refinements, pairing defects, graph coloring, exact matching, realization of
abstract cuts by concrete marks, zero-part removal, and supremum/infimum
bookkeeping.

## 3. AxiomProver time versus Lean verification time

The times in the repository README—between 24 and 869 minutes—should be
understood primarily as AxiomProver's proof-search and proof-construction time,
not the time Lean needs to check the finished proof.

There are two distinct roles:

- **AxiomProver** searches for the mathematical argument and constructs valid
  Lean source.
- **Lean/AXLE** elaborates and checks an already supplied candidate proof.

After installing the pinned Lean toolchain and the prebuilt Mathlib cache, two
complete solution files were elaborated locally:

| Problem | Reported AxiomProver time | Local Lean elaboration |
|---|---:|---:|
| Q2 | 360 minutes | about 33 seconds |
| Q3 | 869 minutes | about 30 seconds |

The measurements are machine-dependent, but the difference in scale is clear.
Q3 took much longer for AxiomProver to discover than Q2, yet the completed Q3
file elaborated slightly faster in this local test. The reported times therefore
do not behave like compilation times.

It is useful to distinguish three tasks:

1. Discover the mathematical argument.
2. express every necessary detail in valid Lean;
3. check the completed proof.

The third task is comparatively cheap. The long autonomous-prover times mostly
belong to the first two. An automated system may explore multiple mathematical
approaches, generate many incomplete Lean candidates, compile them, diagnose
the failures, repair them, and discard unsuccessful branches. Even when each
individual check is inexpensive, many such iterations can accumulate hours of
search time.

Natural-language proof production is faster partly because it permits
compression and ambiguity. A sentence such as “pair the pieces and apply a
pigeonhole argument” may conceal numerous representation choices and auxiliary
claims. It may also conceal a genuine gap. Lean requires every denominator to
be nonzero, every constructed object to satisfy its type, every index to be in
range, and every use of an invariant to have the precise hypotheses required.

Thus the mathematical insight is not necessarily harder in Lean, but converting
that insight into a fully explicit proof is substantially harder. Searching for
both the mathematics and its Lean-compatible implementation at the same time is
harder still. Once the proof is complete, checking it is relatively routine.

## 4. A middle layer: the guided formal proof

A useful compromise is a **guided formal proof**: a human-readable explanation
that remains mechanically anchored to the Lean development.

The material could be presented at three levels:

1. **One-page mathematical idea.** The central construction, invariant, or
   contradiction.
2. **Guided proof.** Each substantive step states the exact formal lemma used,
   explains why it is true, and links to the corresponding Lean declaration.
   Routine representation and coercion details are collapsed into clearly
   labelled notes.
3. **Complete Lean source.** The fully auditable proof, available when every
   obligation needs to be inspected.

For example, the human-facing version of Q3's lower kernel might say:

> Sort the descendant pieces and pair adjacent entries. Their alternating sum
> is exactly the total pairing defect. The pairing induces a graph on the
> original dyadic labels. Because this graph has fewer edges than vertices, it
> has a nontrivial signed component coloring. The corresponding signed sum of
> powers of two is a nonzero integer, so its absolute value is at least one;
> meanwhile, it is bounded above by the pairing defect. Therefore the sorted
> alternating sum is at least one.

This is short enough to read, but it exposes the real formal mechanism rather
than replacing it with another argument.

Traceability is essential. Every mathematical claim in the guided proof should
point to a formal declaration. Conversely, the dependency graph of the main
theorem can help ensure that no conceptually important lemma is omitted from the
human explanation.

## 5. Using formalization difficulty to improve proof design

Formalization difficulty can reveal where a proof architecture is fighting the
system. It helps to classify each difficulty as one of the following:

- **Mathematical difficulty:** a genuinely missing idea or lemma.
- **Representation friction:** repeated conversions among lists, multisets,
  sets, indices, or coordinate systems.
- **Library gap:** a standard mathematical fact is not packaged in a reusable
  form.
- **Automation weakness:** the result is routine, but available tactics do not
  solve it robustly.
- **Computational cost:** normalization, simplification, typeclass search, or a
  decision procedure is consuming disproportionate time.

These categories call for different responses. A mathematical obstacle may
require a new idea; representation friction suggests a better abstraction; a
library gap suggests a reusable lemma; tactic fragility suggests restructuring
the statement or isolating the calculation.

Proofs can often be improved for both humans and Lean by:

- separating the abstract combinatorial theorem from its realization in the
  original problem;
- proving permutation, translation, or scaling invariance once and reusing it;
- choosing inductive definitions that directly match the intended human
  induction;
- replacing repeated element-level bookkeeping with one structural invariant;
- packaging coordinate calculations as explicit Gram-matrix or polynomial
  certificates;
- isolating large computations in lemmas whose statements clearly express their
  mathematical purpose;
- introducing reusable APIs for recurring notions such as refinement, pairing,
  support, or reachability.

Q4 is an example of good alignment: the inductive definition of the winning
predicate naturally matches the human winning-tree induction, and its formal
overhead is modest. Q3 exhibits more representation friction: the proof moves
among marks, gaps, lists, sorted lists, labelled pieces, pairings, graphs, and
abstract refinements. A stronger reusable refinement interface could reduce
both proof-search time and cognitive load.

## 6. Proposed workflow for producing guided proofs

A practical workflow would be:

1. Complete and verify the Lean proof.
2. Extract the declaration-dependency graph of the main theorem.
3. Classify lemmas as mathematical, bridging, bookkeeping, or computational.
4. Preserve the mathematical lemmas in the main narrative.
5. Summarize bridging and bookkeeping lemmas in expandable formalization notes.
6. Link every substantive paragraph to its Lean declaration.
7. Record elaboration time, tactic hotspots, and repeated failed obligations.
8. Use those diagnostics to identify better abstractions or alternative proof
   strategies.
9. Review the guided proof both for human clarity and for fidelity to the
   formal dependency structure.

For this repository, a natural deliverable would be one
`Qn_guided_proof.md` file per problem. Each would sit between the existing
compact informal proof and the complete Lean source, giving mathematicians a
readable but formally traceable account of the verified argument.

## 7. What has actually been verified?

Formal verification applies to a precise Lean proposition, not directly to the
English problem or to the author's intended interpretation. It is useful to
separate the assurance chain into four links:

1. The official problem is translated into mathematical definitions.
2. Those definitions are assembled into a Lean theorem statement.
3. A Lean proof establishes that exact statement from its declared
   assumptions and permitted axioms.
4. A human checks that the formal statement is a faithful model of the source
   problem and that the theorem proved is the result that was intended.

Lean gives very strong assurance for the third link. It does not, by itself,
establish the first, second, or fourth. A perfectly checked proof can still be
irrelevant if a definition is too weak, an important hypothesis has been
omitted, or the conclusion is not a faithful translation of the requested
claim.

The repository's `formalization.yaml` is therefore an important part of the
evidence, rather than merely project metadata. It records modeling decisions
such as:

- Q3 representing optimal play by the alternating sum of sorted piece lengths,
  rather than formalizing the move-by-move claiming game and proving the greedy
  characterization inside this development;
- Q4 reducing a geometric cutting game to multisets of angles and an
  angle-level cut relation;
- Q3, Q4, and Q5 stating the discovered closed-form answer or classification
  explicitly in the main theorem.

These are reasonable choices, but they identify proof obligations at the
boundary between the source problem and the formal model. For a “determine all”
problem, there is also a conceptual distinction between *discovering* the
answer and *verifying* a proposed classification. The final Lean theorem gives
high assurance for the latter; the prover's search process supplied the former.

The solution files contain no `sorry`, and the project metadata reports only
the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for the main
results. The `sorry` declarations in the separate `problem.lean` files are
placeholders for specifications; they do not support the proofs in the
standalone `solution.lean` files, which restate and prove their results. This
distinction should remain visible in any audit.

The practical lesson is that a verified result needs two complementary reviews:
a kernel-level proof check and a source-to-statement fidelity review. Neither is
a substitute for the other.

## 8. A more complete cost model

Line count and elapsed prover time measure only parts of the cost. A useful
comparison separates the proof lifecycle:

| Stage | Informal proof | Formal proof |
|---|---|---|
| Problem interpretation | Usually implicit and cheap, but ambiguity may survive | Definitions force many choices to be made, but still require human validation |
| Mathematical discovery | Fast to sketch and revise | May be interleaved with expensive proof search and failed elaboration attempts |
| Representation and library work | Mostly absent | Can dominate when the available abstractions do not match the argument |
| Proof construction | Compresses routine steps | Must discharge every logical, typing, and side-condition obligation |
| Checking | Expert reading; relatively slow and variable | Kernel checking is repeatable and comparatively cheap once the proof exists |
| Exposition | The proof itself can be the explanation | Usually requires a separate narrative or guided layer |
| Maintenance | Robust to notation and library changes, but regressions are hard to detect mechanically | Changes are detected automatically, although repairs after library or representation changes may be costly |
| Reuse | Ideas are reusable by a reader | Definitions and lemmas can become checked infrastructure for later proofs |

This reveals several different quantities that should not be collapsed into a
single “cost of proof”:

- human mathematical time;
- human formalization and debugging time;
- autonomous search time;
- compute consumption, including unsuccessful branches;
- review time for the statement and modeling choices;
- kernel-checking time;
- exposition and maintenance time.

These costs also have different units. Wall-clock minutes on a parallel agent
system are not equivalent to CPU or accelerator hours, monetary cost, energy,
or expert labor. Likewise, final source length does not reveal how many failed
approaches were tried or how much of the file was generated from reusable
infrastructure. The present measurements demonstrate a real elaboration-size
and search-time gap, but they are not yet a full economic comparison.

Formalization has a substantial fixed cost and potentially low marginal costs.
The first proof using a representation may require a large API; later proofs
can reuse it. An informal proof often has a lower initial cost, while each new
reader may pay part of the checking cost again. Consequently, the relevant
question is not only “Which proof is cheaper to produce once?” but also “How
many times will it be checked, adapted, composed, or maintained?”

## 9. Assurance, readability, and reuse are separate objectives

Informal and formal proofs should not be placed on a single quality scale. They
optimize different objectives:

- **Informal proofs** are effective for exploration, communication, intuition,
  and rapid comparison of strategies.
- **Formal proofs** are effective for exact checking, dependable composition,
  regression detection, and reuse by other formal developments.
- **Guided proofs** aim to transfer the assurance of the formal artifact into a
  form that a human can navigate, without pretending that the narrative itself
  has been kernel-checked.

A long Lean file is not automatically explanatory, and a beautiful informal
proof is not automatically complete. Nor does formal verification eliminate
all trust. One must still trust the Lean kernel and toolchain, the meanings of
the imported definitions, and the fidelity of the formal statement. The
benefit is that this trusted base is explicit and much smaller than the body of
reasoning being checked.

The best allocation can therefore vary by use case. During discovery, a short
informal proof may be the right artifact. For a stable theorem that will support
many downstream results, formalization becomes more valuable. For a
competition solution whose main purpose is education, the readable proof
remains indispensable even when a formal certificate exists. In this
repository, retaining all three layers is more informative than selecting one
as the universal replacement for the others.

## 10. Maintenance and robustness

Formal proofs provide an unusually strong regression test: if a definition,
hypothesis, or imported theorem changes incompatibly, elaboration fails. This
is valuable, but it does not mean that formal proofs are maintenance-free.
Proof scripts may be sensitive to:

- changes in Mathlib theorem names or simp sets;
- different elaboration or typeclass-search behavior;
- reliance on large automation calls whose success is sensitive to context;
- low-level representations that expose many implementation details;
- theorem statements that are stronger or more specialized than future reuse
  requires.

Informal proofs have almost the opposite profile. They often survive notation
and library changes, but a changed assumption can silently invalidate a
paragraph. Their semantic robustness comes with weak automatic regression
detection.

For a fair longitudinal comparison, maintenance should be measured as well as
initial construction. Useful signals include the number of declarations
affected by a small statement change, repair time after a Mathlib upgrade, the
fraction of the proof concentrated in stable domain lemmas, and whether the
guided explanation remains aligned after formal refactoring.

## 11. Suggested measurements for this case study

The six problems are large enough to expose different sources of difficulty,
but small enough to support a more systematic study. For each problem, one
could record:

1. Discovery time, formal construction time, and final checking time
   separately.
2. Total compute used across successful and unsuccessful attempts, not only
   elapsed time for the successful run.
3. Human interventions, including statement repair, hints, library search, and
   review.
4. Final source size, declaration count, dependency count, and the proportion
   classified as mathematical versus representational bookkeeping.
5. Clean-build and incremental elaboration times under a pinned environment.
6. The axioms and unfinished-proof mechanisms on which each main theorem
   depends.
7. Modeling divergences found during source-to-statement review.
8. Gaps found while turning the informal proof into Lean, and gaps found while
   translating Lean back into a guided proof.
9. Reader time and error rate for answering comprehension questions from the
   informal proof, guided proof, and raw Lean source.
10. Repair effort after a controlled change to a definition, hypothesis, or
    library version.

This would produce a *cost-to-assurance profile* rather than a single overhead
ratio. For example, Q3 may be expensive in construction and exposition but
especially valuable as a reusable formal combinatorial development; Q4 may
show that a representation aligned with the mathematical induction can be both
compact and robust. Such distinctions are lost in an aggregate 7.2x line
ratio.

The study should also avoid treating the final informal proofs as if they were
independent controls: they were revised after comparison with the Lean proofs.
That is valuable evidence for a hybrid workflow, but it means the polished
informal artifacts already contain benefits from formalization. A controlled
comparison would preserve the initial drafts, the issues detected at each
review stage, and the final revisions.

## 12. The model and the harness should be evaluated together

A further practical observation from this exploration is that Meta's
[Muse Spark](https://ai.meta.com/blog/introducing-muse-spark-msl/) model and
the Muse Code harness worked well together. This was the author's first
experience with both, so the result is best treated as a useful case study
rather than a controlled benchmark or a claim of general superiority.

The experience reinforces that an autonomous prover or coding agent is not
just a language model. The effective system also includes the harness that
decides what context to provide, which tools to expose, how to preserve state,
when to run Lean, how to present elaborator errors, when to retry, and when a
candidate proof is complete. On formal-proof tasks this feedback loop is
especially important: Lean supplies an exact acceptance test, but the harness
must turn failed checks into productive next actions.

This has two consequences for the cost discussion. First, success and failure
cannot automatically be attributed to the base model. A good harness may reduce
duplicated exploration, retain useful context, isolate concurrent work, and
verify edits promptly; a poor harness can waste a strong model's tokens on
repeated searches or allow it to stop at an unchecked candidate. Second,
harness behavior affects nearly every quantity one might measure: wall-clock
time, token use, tool calls, parallel compute, human steering, and the number of
discarded proof attempts.

Future experiment logs should therefore record the model and harness as a
pair, including their versions and relevant configuration. Where interfaces
permit it, a stronger experiment would cross several models with several
harnesses on the same pinned repository state. Repeated runs should report both
proof acceptance and resource use. That would help distinguish three possible
sources of performance:

- the model's mathematical and coding ability;
- the harness's context, search, and verification policy;
- the compatibility produced by tuning a model for a particular harness and
  tool protocol.

For the present notes, the warranted conclusion is narrower but still
important: Muse Spark plus Muse Code was an effective working combination in
this first hands-on use, and the experience makes “model versus model” an
incomplete framing for comparisons of formal-proof systems.

## Discussion questions

- What level of formal detail does a mathematician need before trusting that a
  summary faithfully represents the verified proof?
- Should guided proofs follow the actual formal proof exactly, or may they
  present a cleaner equivalent proof when the difference is clearly disclosed?
- Can dependency graphs and elaboration metrics identify the lemmas that deserve
  the most explanatory attention?
- Which kinds of Lean difficulty are evidence of mathematical complexity, and
  which are artifacts of representation or library design?
- Should optimization target compilation time, autonomous proof-search time,
  source length, human readability, or some combination of these objectives?
- What reusable abstractions from these six problems would most reduce the cost
  of formalizing future olympiad mathematics?
- How much of the assurance budget should be spent on checking the proof, and
  how much on validating the translation of the original problem?
- At what expected level of reuse does the fixed cost of formalization become
  worthwhile?
- How should failed search attempts and total compute be reported so that
  autonomous and human-assisted proof efforts can be compared fairly?
- How much of an observed performance difference belongs to the model, the
  harness, or the fit between them?
