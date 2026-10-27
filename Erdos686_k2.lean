import Mathlib.Tactic

/-!
Probleme Erdos #686 (erdosproblems.com/686), cas particuliers k = 2.

Question du probleme 686 (OUVERT, non resolu ici) :
  tout N >= 2 s'ecrit-il  N = prod_{i=1..k}(m+i) / prod_{i=1..k}(n+i)
  pour un k >= 2 et un m >= n + k ?

Ce fichier ne resout PAS ce probleme. Il contient :
  A. la definition et deux lemmes de calcul ;
  B. quatre cas particuliers de non-representabilite en k = 2 ;
  C. des exemples de N representables en k = 2 avec m >= n + k ;
  D. un enonce trivial (SANS m >= n + k), garde pour memoire.
-/

-- A. Definition : P k m = (m+1)(m+2)...(m+k)
def P (k m : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc * (m + i + 1)) 1

lemma P_succ (k m : Nat) : P (k+1) m = P k m * (m + k + 1) := by
  unfold P
  rw [List.range_succ, List.foldl_append]
  simp

lemma P_two (m : Nat) : P 2 m = (m+1)*(m+2) := by
  have h1 : P 1 m = m+1 := by unfold P; simp
  have h2 : P 2 m = P 1 m * (m+2) := P_succ 1 m
  rw [h2, h1]

-- B. Non-representabilite en k = 2 (preuves reprises de l'issue #493, non modifiees).
-- Ces enonces sont plus forts que necessaire : ils n'imposent pas m >= n + 2.

theorem no_solution_4_k2 (m n : Nat) : P 2 m ≠ 4 * P 2 n := by
  rw [P_two, P_two]; intro h
  set X : ℤ := 2*m + 3; set Y : ℤ := 2*n + 3
  have hXY : X^2 = 4*Y^2 - 3 := by simp only [X, Y] at *; nlinarith
  have h_lt : X < 2*Y := by nlinarith
  have h_ge : X ≥ 2*Y - 1 := by nlinarith
  have h_eq : X = 2*Y - 1 := by omega
  have : Y = 1 := by rw [h_eq] at hXY; nlinarith
  omega

theorem P2_odd_square_9 : ∀ m n, P 2 m ≠ 9 * P 2 n := by
  intro m n; rw [P_two, P_two]; intro h
  set X : ℤ := 2*m + 3; set Y : ℤ := 2*n + 3
  have hY : Y ≥ 3 := by simp [Y]
  have hXY : X^2 = 9*Y^2 - 8 := by simp only [X, Y] at *; nlinarith
  have h_lt : X < 3*Y := by nlinarith
  have h_ge : X ≥ 3*Y - 1 := by nlinarith
  have h_eq : X = 3*Y - 1 := by omega
  have h_expand : (3*Y - 1)^2 = 9*Y^2 - 6*Y + 1 := by ring
  rw [h_eq] at hXY; rw [h_expand] at hXY; omega

theorem P2_odd_square_25 : ∀ m n, P 2 m ≠ 25 * P 2 n := by
  intro m n; rw [P_two, P_two]; intro h
  set X : ℤ := 2*m + 3; set Y : ℤ := 2*n + 3
  have hY : Y ≥ 3 := by simp [Y]
  have hXY : X^2 = 25*Y^2 - 24 := by simp only [X, Y] at *; nlinarith
  have h_lt : X < 5*Y := by nlinarith
  have h_ge : X ≥ 5*Y - 2 := by nlinarith
  have h_cases : X = 5*Y - 1 ∨ X = 5*Y - 2 := by omega
  rcases h_cases with heq | heq
  · have h_expand : (5*Y - 1)^2 = 25*Y^2 - 10*Y + 1 := by ring
    rw [heq] at hXY; rw [h_expand] at hXY; omega
  · have h_expand : (5*Y - 2)^2 = 25*Y^2 - 20*Y + 4 := by ring
    rw [heq] at hXY; rw [h_expand] at hXY; omega

theorem P2_odd_square_49 : ∀ m n, P 2 m ≠ 49 * P 2 n := by
  intro m n; rw [P_two, P_two]; intro h
  set X : ℤ := 2*m + 3; set Y : ℤ := 2*n + 3
  have hY : Y ≥ 3 := by simp [Y]
  have hXY : X^2 = 49*Y^2 - 48 := by simp only [X, Y] at *; nlinarith
  have h_lt : X < 7*Y := by nlinarith
  have h_ge : X ≥ 7*Y - 3 := by nlinarith
  have h_cases : X = 7*Y - 1 ∨ X = 7*Y - 2 ∨ X = 7*Y - 3 := by omega
  rcases h_cases with heq | heq | heq
  · have h_expand : (7*Y - 1)^2 = 49*Y^2 - 14*Y + 1 := by ring
    rw [heq] at hXY; rw [h_expand] at hXY; omega
  · have h_expand : (7*Y - 2)^2 = 49*Y^2 - 28*Y + 4 := by ring
    rw [heq] at hXY; rw [h_expand] at hXY; omega
  · have h_expand : (7*Y - 3)^2 = 49*Y^2 - 42*Y + 9 := by ring
    rw [heq] at hXY; rw [h_expand] at hXY; omega

-- C. Exemples representables en k = 2, AVEC m >= n + k (donc fideles a l'enonce du 686).
-- Ils montrent qu'il n'existe pas de regle du type "les carres impairs sont exclus".

theorem ex_N2 : (19 ≥ 13 + 2) ∧ P 2 19 = 2 * P 2 13 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [P_two]

theorem ex_N3 : (8 ≥ 4 + 2) ∧ P 2 8 = 3 * P 2 4 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [P_two]

theorem ex_N36 : (7 ≥ 0 + 2) ∧ P 2 7 = 36 * P 2 0 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [P_two]

-- 1225 = 35^2 est un carre impair : il est representable, contrairement a ce qu'affirmait l'issue #493.
theorem ex_N1225 : (48 ≥ 0 + 2) ∧ P 2 48 = 1225 * P 2 0 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [P_two]

-- D. Version SANS la condition m >= n + k : trivialement vraie, ce n'est PAS le probleme 686.
lemma P_one_mul (k : Nat) : P k 1 = (k+1) * P k 0 := by
  induction k with
  | zero => unfold P; simp
  | succ k ih => rw [P_succ, P_succ, ih]; ring

theorem version_triviale_sans_disjonction (N : Nat) (hN : N ≥ 3) :
    ∃ k m n, k ≥ 2 ∧ P k m = N * P k n := by
  have h := P_one_mul (N-1)
  have hN1 : N-1+1 = N := by omega
  rw [hN1] at h
  exact ⟨N-1, 1, 0, by omega, h⟩

/- Enonce FIDELE du probleme 686 (non prouve ; probleme ouvert) :

theorem erdos_686 (N : Nat) (hN : N ≥ 2) :
    ∃ k m n, k ≥ 2 ∧ m ≥ n + k ∧ P k m = N * P k n

-/
