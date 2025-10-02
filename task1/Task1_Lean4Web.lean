/- Copyright (c) Kelin Luo, 2025.  All rights reserved. -/ 
-- Instructions for Lean Task Project
-- 1. Coding Environment
--     * You may complete your Lean code directly in the online editor: https://live.lean-lang.org/
--     * After finishing your work, please save your file and keep a copy of the code for submission.
-- 2. Learning Resources
--     * You may consult official Lean learning materials: https://leanprover-community.github.io/learn.html
-- 3. Use of AI Tools
--     * You are allowed to use AI tools such as ChatGPT, GitHub Copilot, etc. to support your coding and proofs.
--     * If you use these tools, please include the prompts you used in your submission.
--     * Add these prompts as comments in your Lean file (e.g., starting with -- Prompt:), so we know what questions you asked and how you used AI for assistance.
-- 4. Submission Format
--     * Ensure your Lean file is clean, well-commented, and compiles correctly.
--     * Clearly separate your own solutions from AI references.
 

/- Task 1: 12 points (worth 2.5% of your final grade).-/
import Mathlib
import Mathlib.Tactic

/-! # Section 0: Math Basics (4 points) -/

/-! ## Example and Exercise: equation and inequality -/

-- Example 0.1
example {a b : ℝ} (h1 : a = 3) (h2 : b = -1) : a + b = 2 :=
  calc 
    a + b = 3 + b := by rw [h1]    -- Replace a with 3 using the given hypothesis
    _ = 3 + (-1) := by rw [h2]   -- Replace b with -1 using the given hypothesis 
    _ = -1 + 3 := by rw [add_comm]   -- Swap the terms with add_comm
    _ = 2:= by norm_num   -- norm_num is a tactic that simplifies numeric expressions

-- (1 point) Exercise 0.1
example {a b : ℝ} (h1 : a = 3) (h2 : b = 4) : a + 2 * b = 11 :=
  sorry

-- Example 0.2
example {n : ℕ} (h1 : c = 1) : 2 * n + 10 ≥ c * 2 := by
  rw [h1]   -- Replace c with 1 using the given hypothesis
  simp    -- Simplify the expression  

-- (1 point) Exercise 0.2
example {n : ℕ} (h1 : c = 3) : 5 * n + 6 ≥ c := by
  sorry 

-- Example 0.3
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]    -- Replace c with 5 using the given hypothesis
  calc    -- Use calc to structure the proof
    4 * n ≤ 5 * n := by
      have h : 0 ≤ n := Nat.zero_le n    --  State a fact h: natural numbers are nonnegative
      linarith    -- linarith is a tactic that automatically solves linear inequalities using facts in context

-- Example 0.3 (Another option)
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]
  linarith    -- linarith handles the inequality 4n ≤ 5n automatically

-- (1 point) Exercise 0.3
example  {n : ℕ} (h1 : c = 2) : 4 * n + 3 ≥ c * (n + 1) := by
  sorry

-- Example 0.4
example {n : ℕ} (h1 : n ≥ 1) (h2 : c = 1) : 12 * n^2 ≥ c * (2 * n + 10) := by
  calc
    12 * n^2 = 12 * n * n         := by ring
    _ ≥ 2 * n + 10                := by nlinarith
    _ = 1 * (2 * n + 10)          := by ring
    _ = c * (2 * n + 10)          := by rw [h2]

-- Example 0.5
example {n : ℕ} (h1 : n ≥ 2) (h2 : c₁ = 1) (h3 : c₂ = 4) :
  c₁ * n ≤ 2 * n + 5 ∧ n + 1 ≤ c₂ * n := by
  rw [h2, h3]
  constructor
  linarith [h1]    -- prove n ≤ 2n + 5, true since n ≥ 2
  linarith [h1]    -- prove n + 1 ≤ 4n, true since n ≥ 2

 -- (1 point) Exercise 0.4
example {n : ℕ} (h1 : n ≥ 10) (h2 : c₁ = 1) (h3 : c₂ = 10) :
  c₁ * (2 * n + 1) ≤ 5 * n ∧ 5 * n ≤ c₂ * (2 * n + 1) := by
  sorry


/-! # Section 1: Asymptotic Analysis in Lean (5 points) -/
-- This file includes: Big-O, Big-Omega, Big-Theta notation and exercises

/-! ## Definition of Asymptotic Notation -/

--  Example 1.1: Definition of Big-O (O)
def isBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c n₀ : ℝ), 0 < c ∧ ∀ (n : ℕ), (n ≥ n₀) → (f n ≤ c * g n)

-- (1 point) Exercise 1.1: Definition of Big-Omega (Ω) 
def isBigOmega (f g : ℕ → ℝ) : Prop :=
  sorry

-- (1 point) Exercise 1.2: Definition of Big-Theta (Θ) (Please use Big-O and Big-Omega definitions)
def isBigTheta (f g : ℕ → ℝ) : Prop :=
  sorry

/-! ## Asymptotic Analysis Proof-/

-- Example 1.2: 2n + 4 ∈ O(n)
example : isBigO (fun n ↦ (2 : ℝ) * n + 4) (fun n ↦ n) := by
  use 3, 4
  constructor
  · linarith                      -- show 3 > 0
  intro n hn
  calc
    (2 : ℝ) * n + 4 ≤ 2 * n + n := by linarith [hn]  -- since n ≥ 4
    _ = 3 * n := by ring

-- (1 point) Exercise 1.3: show 3n + 2 ∈ O(n)
example : isBigO (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

-- (1 point) Exercise 1.4: show 3n + 2 ∈ Ω(n)
example : isBigOmega (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

-- (1 point) Exercise 1.5: show 3n + 2 ∈ Θ(n)
example : isBigTheta (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

/-! # Section 2: Induction Proof in Lean (3 points) -/

-- Example 2.1: Define the function sumNR(n) using well-founded recursion and prove the closed-form formula
-- Simple recursive sum over ℝ
def sumNR : ℕ → ℝ
  | 0     => 0
  | n + 1 => sumNR n + (n + 1)

-- ∑_{i=1..n} i = n(n+1)/2
example (n : ℕ) : sumNR n = n * (n + 1) / 2 := by
  induction n with
  | zero =>
      simp [sumNR]
  | succ k IH =>
      -- sumNR (k+1) = sumNR k + (k+1)
      -- use IH and ring
      simp [sumNR, IH]
      ring

-- (2 points) Exercise 2.1: Define the function sumOdd(n) using well-founded recursion and prove the closed-form formula 
-- Define sum of odds recursively
def sumOdd : ℕ → ℕ
  | 0     => 1
  | n + 1 => sumOdd n + (2 * (n + 1) + 1)

-- Closed form: ∑_{i=0}^n (2i+1) = (n+1)^2
example (n : ℕ) : sumOdd n = (n + 1) ^ 2 := by
  induction n with
  | zero =>
    -- Base case: n = 0
    sorry
  | succ k IH =>
    -- Inductive step: assume sumOdd k = (k+1)^2
    sorry 

-- (1 point) Exercise 2.2: Define the Fibonacci function fib(n)




