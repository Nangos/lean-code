/- https://leetcode.com/problems/two-sum/

## Original problem statement:
Given an array of integers nums and an integer target, return indices of the two numbers
such that they add up to target.

You may assume that each input would have exactly one solution, and you may not use the
same element twice.

You can return the answer in any order.

## Adaption for formal verification:
- Having "exactly one solution" does NOT simplify the problem in any significant way, but will
make the specification and proof more verbose. Instead, we simply assume that there exists
(at least) one solution.

## Examples:
Example 1:
Input: nums = [2,7,11,15], target = 9
Output: [0,1]
Explanation: Because nums[0] + nums[1] == 9, we return [0, 1].

Example 2:
Input: nums = [3,2,4], target = 6
Output: [1,2]

Example 3:
Input: nums = [3,3], target = 6
Output: [0,1]
-/

import Std.Data.HashMap
open Std

namespace TwoSum

/-- Two *distinct* indices `i` and `j` form a solution if `nums[i] + nums[j] = target`. -/
def isSolution (nums : Array Int) (target : Int) (i j : Fin nums.size) : Prop :=
  i ≠ j ∧ nums[i] + nums[j] = target

/-- The relation `isSolution` is symmetric in `i` and `j`. -/
theorem isSolution.symm (nums : Array Int) (target : Int) (i j : Fin nums.size) :
    isSolution nums target i j ↔ isSolution nums target j i := by
  simp [isSolution]; omega

/-- The **triangular** property: WLOG assume `j < i` when searching for a solution. -/
theorem existsSolution_trangular (nums : Array Int) (target : Int) :
    (∃ i j, isSolution nums target i j) ↔ (∃ i, ∃ j < i, isSolution nums target i j) := by
  constructor
  · -- "→": Given a solution `(i, j)`, we can WLOG assume `j < i` by symmetry.
    rintro ⟨i, j, hIsSolution⟩
    have hNeq : i < j ∨ j < i := by simp [isSolution] at *; omega
    cases hNeq with
    | inl hILtJ => exists j, i; simp [isSolution.symm]; trivial
    | inr hJLtI => exists i, j
  · -- "←": Obvious.
    rintro ⟨i, j, hJLtI, hIsSolution⟩
    exists i, j

/-- Same as `Std.HashMap`. Merely a trick for on-demand dot notation. -/
abbrev HashMap' := HashMap

/-- The `stores` relation: the hashmap `map` stores the first `n` elements of `nums`. -/
def HashMap'.stores (nums : Array Int) (n : Fin (nums.size + 1))
    (map : HashMap' Int (Fin nums.size)) : Prop :=
  (∀ k i, map.get? k = some i → i.val < n.val ∧ nums[i] = k) ∧
  (∀ k, map.get? k = none → ∀ i : Fin n, nums[i] ≠ k)

/-- The recursive helper function for `twoSum`, assuming the first `n` elements are processed. -/
def twoSumSub (nums : Array Int) (target : Int) (n : Fin (nums.size + 1))
    (hExistsSub : ∃ i, i.val ≥ n.val ∧ ∃ j < i, isSolution nums target i j)
    (map : HashMap' Int (Fin nums.size))
    (hMapValid : map.stores nums n)
    : Σ' i j, isSolution nums target i j :=
  if hInBound : n < nums.size then
    let i := n.castLT hInBound
    let complement := target - nums[i]
    match map.get? complement with
    | some j =>  -- Found a solution!
      have hIsSolution : isSolution nums target i j := sorry
      ⟨i, j, hIsSolution⟩
    | none =>  -- Recursively process the rest of the array.
      let n' := ⟨n.val + 1, by omega⟩
      have hExistsSub' : ∃ i, i.val ≥ n.val + 1 ∧ ∃ j < i, isSolution nums target i j := sorry
      let map' : HashMap' .. := map.insert nums[i] i
      have hMapValid' : map'.stores nums n' := sorry
      twoSumSub nums target n' hExistsSub' map' hMapValid'
  else  -- Actually unreachable, so below is just proof by contradiction.
    absurd hExistsSub (by omega)

/-- The main `twoSum` algorithm. Given a solution `(i, j)` exists, find such one. -/
def twoSum (nums : Array Int) (target : Int)
    (hExists : ∃ i j, isSolution nums target i j)
    : Σ' i j, isSolution nums target i j :=
  have hExistsSub : ∃ i, i.val ≥ 0 ∧ ∃ j < i, isSolution nums target i j := sorry
  let map : HashMap' .. := {}
  have hMapValid : map.stores nums 0 := sorry
  twoSumSub nums target 0 hExistsSub map hMapValid


-- ## Finished!! Now it's time to see our program in action.

/-- Extract the solution from the `Σ'` type returned by `twoSum`. -/
def extract {nums target} (r : Σ' i j, isSolution nums target i j) : Nat × Nat :=
  let ⟨i, j, _⟩ := r
  (i.val, j.val)

-- ### Simple Running Examples:

/-- info: (1, 0) -/
#guard_msgs in
#eval! extract <| twoSum #[2, 7, 11, 15] 9 (by simp [isSolution]; decide)

/-- info: (2, 1) -/
#guard_msgs in
#eval! extract <| twoSum #[3, 2, 4] 6 (by simp [isSolution]; decide)

/-- info: (1, 0) -/
#guard_msgs in
#eval! extract <| twoSum #[3, 3] 6 (by simp [isSolution]; decide)

-- ### Performance Test:

/-- Creates a worst-case array of size N with all elements being 0, then appends two 1's.
    Prints the time elapsed. Note that `twoSum` is expected to find a solution in O(N) time. -/
def performanceTest (N : Nat) : IO Unit := do
  let nums := Array.replicate N (0 : Int) ++ #[1, 1]
  let target : Int := 2
  have hExists : ∃ i j, isSolution nums target i j := by
    have : nums.size = N + 2 := by simp [nums]
    exists ⟨N + 1, by simp [*]⟩, ⟨N, by simp [*]⟩
    simp [isSolution, nums, target]

  let start ← IO.monoMsNow
  let solution := extract <| twoSum nums target hExists
  IO.println s!"[N={N+2}] Found solution: {solution}"
  let finish ← IO.monoMsNow

  let elapsed := finish - start
  IO.println s!"Elapsed time: {elapsed}ms"

end TwoSum

/- Try this in `LeanCode.lean` to see the REAL performance:
import LeanCode.G00.P0001_TwoSum
def main : IO Unit := do
  TwoSum.performanceTest    100_000
  TwoSum.performanceTest  1_000_000
  TwoSum.performanceTest 10_000_000
$ lake exe perf_test
-/
