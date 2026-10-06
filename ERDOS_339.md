# Erdős 339: statement account and audit limits

Prepared 6 October 2026. This document accompanies the supplied Lean development;
it is not a completed mathematical or kernel audit.

## Compared statements

For A ⊆ ℕ and r ∈ ℕ, let U≤r(A) be all sums of at most r elements of A,
with repetitions allowed, and let Rr(A) be all sums of exactly r distinct elements.
Let d_lower and d_upper denote lower and upper natural densities, using counts
in {1,…,N} divided by N. The four quantified claims are:

1. For every A and r, if every sufficiently large n is in U≤r(A), then
   d_lower(Rr(A)) > 0 (`Erdos339.erdos_339`).
2. For every A and r, if every sufficiently large n is in the exact-r unrestricted
   sumset r • A, then d_lower(Rr(A)) > 0 (`Erdos339.erdos_339_exact`).
3. For every A and r, if d_upper(U≤r(A)) > 0, then d_upper(Rr(A)) > 0
   (`Erdos339.erdos_339_upper`).
4. For every A and r, if d_upper(r • A) > 0, then d_upper(Rr(A)) > 0
   (`Erdos339.erdos_339_upper_exact`).

The unrestricted multiset representations allow repetitions, and allow the empty
sum. Restricted representations are finite sets of cardinality exactly r, so
repetitions are excluded. The source handles order zero and finite A explicitly;
no hidden positivity-of-r assumption was added to the compared theorems.

## Definitions and correspondence

| Mathematical notion | Lean declaration |
| --- | --- |
| At-most-r sums with repetitions | `sumsAtMost` |
| Eventual at-most-r basis property | `IsAddBasisOfOrder` |
| Exactly-r restricted sums | `distinctSums` |
| Counting on {1,…,N} | `countUpTo` |
| Lower density | `lowerDensity` |
| Upper density | `upperDensity` |
| Exactly-r unrestricted sumset | `r • A` with scoped Pointwise notation |

At N=0 the real quotient is Lean's zero-division value; changing one term does
not affect the density at infinity. Counts are bounded between zero and N.

## Supplied proof architecture

A finite counting lemma bounds arbitrary sums b+x by a constant times sums whose
partner x is not in a forbidden set. The isolation step makes a coordinate of a
representing tuple distinct from all others at a cost 1+r(r+1) and doubles the
counting range. Iterating over r coordinates yields restricted representations.
Zero-padding converts at-most-r sums into r-tuples over A ∪ {0}. Bounded shifts
remove a possible padded zero. The resulting counting bound yields positive
lower density for bases and positive upper density when unrestricted sums have
positive upper density. The exact-r variants follow by inclusion.

This describes the supplied code, not an independently verified mathematical
proof. No theorem in this package has been compiled during packaging.

## Sources and known-result status

The attachment attributes the two density results to Hegyvári, Hennecart and
Plagne, *A proof of two Erdős' conjectures on restricted addition and further
results*, J. reine angew. Math. 560 (2003), 199–220, DOI 10.1515/crll.2003.055.
The indexed Erdős 339 entry corroborates that attribution. The original paper
was not read in full here, and no claimed correspondence to a specific numbered
paper theorem has been independently verified. The source's at-most-r convention
also requires a full check against https://www.erdosproblems.com/definitions.
This is a development for known results, not a newly claimed solution.

No novelty or absence of prior Lean formalizations is established. The proof text
was supplied by the user; its earlier generation history is unknown. AI prepared
the package. No independent human review is claimed. The repository snapshot is
licensed under MIT; this does not relicense cited papers or dependencies.

## Trust and verification

No sorry, admit, unsafe declaration, newly declared axiom, or native_decide occurs
in the supplied proof code. This is not a claim of literal axiom freedom:
Comparator permits propext, Quot.sound and Classical.choice. Actual dependencies
must be checked after compilation. Challenge and Solution are distinct modules
containing independent copies of the same statements and supplied proof text.
Challenge has proofs too, avoiding placeholder sorries at the cost of a larger
statement file. It remains below the hard 1,000-line and 100-KiB limits.
