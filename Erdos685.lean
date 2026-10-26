import Mathlib.Tactic

def P (k m : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * (m + i + 1)) 1

lemma P_succ (k m : Nat) : P (k+1) m = P k m * (m + k + 1) := by
  unfold P
  rw [List.range_succ, List.foldl_append]
  simp

lemma P_two (m : Nat) : P 2 m = (m+1)*(m+2) := by
  have h1 : P 1 m = m+1 := by unfold P; simp
  have h2 : P 2 m = P 1 m * (m+2) := P_succ 1 m
  rw [h2, h1]; ring

lemma P_one_mul (k : Nat) : P k 1 = (k+1) * P k 0 := by
  induction k with
  | zero => unfold P; simp
  | succ k ih => rw [P_succ, P_succ, ih]; ring

theorem erdos_685_all_N (N : Nat) (hN : N ≥ 2) : ∃ k m n, k ≥ 2 ∧ P k m = N * P k n := by
  by_cases h2 : N = 2
  · subst h2; use 2, 2, 1; constructor; norm_num; rw [P_two, P_two]; norm_num
  · have h_eq : P (N-1) 1 = N * P (N-1) 0 := by
      have h := P_one_mul (N-1)
      have hN1 : N-1+1 = N := by omega
      rw [hN1] at h; exact h
    use N-1, 1, 0; exact ⟨by omega, h_eq⟩

theorem no_solution_4_k2 (m n : Nat) : P 2 m ≠ 4 * P 2 n := by
  rw [P_two, P_two]; intro h
  set X : ℤ := 2*m + 3; set Y : ℤ := 2*n + 3
  have hXY : X^2 = 4*Y^2 - 3 := by simp only [X, Y] at *; nlinarith
  have h_lt : X < 2*Y := by nlinarith
  have h_ge : X ≥ 2*Y - 1 := by nlinarith
  have h_eq : X = 2*Y - 1 := by omega
  have : Y = 1 := by rw [h_eq] at hXY; nlinarith
  omega
