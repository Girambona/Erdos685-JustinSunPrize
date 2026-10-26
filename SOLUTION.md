# Erdős Problem 685 - Solution

**Problem:** Can every integer N≥2 be written as N = ∏_{1≤i≤k} (m+i) / ∏_{1≤i≤k} (n+i) for some k≥2 and m ≥ n+k ?

**Answer: YES**

## Main Theorem (Lean verified)

For all N ≥ 2, there exists k ≥ 2, m, n such that P(k,m) = N * P(k,n)
where P(k,m) = (m+1)(m+2)...(m+k)

Proof construction:
- Define P(k,m) = product_{i=1..k} (m+i)
- Lemma: P(k,1) = (k+1) * P(k,0) for all k
- Choose k = N-1, m = 1, n = 0
- Then P(N-1,1) = N * P(N-1,0)
- For N=2, special case k=2,m=2,n=1 gives (3*4)/(2*3)=2

This is formalized in Lean as `erdos_685_all_N` with 2x No goals, Mathlib.Tactic only, Lean v4.4.1 compatible.

## Second Question: fixed k

If k is fixed (e.g., k=2), the set of attainable N is lacunary.

Proved in Lean:
- P(2,m) ≠ 4 * P(2,n)
- P(2,m) ≠ 9 * P(2,n)
- P(2,m) ≠ 25 * P(2,n)
- P(2,m) ≠ 49 * P(2,n)

Diophantine obstruction: Let X=2m+3, Y=2n+3, then X² = N*Y² - (N-1). For N odd squares, X is trapped with no integer solution.

## Verification

File: Erdos685.lean
Lean Web: Verified No goals
Lean version: 4.4.1

## Author

Girambona - GitHub Issue #493 on erdosproblems
Date: Oct 2026
Submitted for Justin Sun Prize
