Here’s a clean, copy-paste **README.md** tailored to your Task 1 project.

---

# CSE 431/531 — Task 1: Lean Introduction

**Author:** Kelin Luo
**Course weight:** 12 points (worth 2.5% of final grade)

This project demonstrates basic Lean usage, asymptotic analysis (O/Ω/Θ), and induction proofs. All proofs compile and can be checked by Lean’s kernel.

---

## What’s included

* **Section 0 — Math Basics (4 pts):**
  Small equalities/inequalities using `simp`, `rw`, `linarith`, `ring`.
  Examples & exercises: numeric rewrites, linear bounds, splitting conjunctions with `constructor`.

* **Section 1 — Asymptotic Analysis (5 pts):**
  Custom definitions of **Big-O**, **Big-Omega**, **Big-Theta**, and short proofs such as
  $2n+4 \in O(n)$, $3n+2 \in O(n)$, $3n+2 \in \Theta(n)$.

* **Section 2 — Induction (3 pts):**
  Recursive definitions with closed forms:

  * `sumNR n = ∑_{i=1}^{n} i` with formula $n(n+1)/2$ over ℝ,
  * `sumOdd n = ∑_{i=0}^{n} (2i+1)` with formula $(n+1)^2$ over ℕ,
  * `fib` (Fibonacci) by double recursion.

All code is in a single Lean file (see **File layout** below) and compiles without `sorry`.

---

## How to build & view

### Option A — Local (recommended)

1. **Install Lean/Lake via elan** (adds tools to PATH):

   ```powershell
   iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
   ```

   Restart your terminal, then verify:

   ```powershell
   lean --version
   lake --version
   ```

2. **Create/open the project** (if not already):

   ```powershell
   lake new task1 math
   cd task1
   ```

   Open the folder in VS Code:

   ```powershell
   code .
   ```

3. **Build (downloads mathlib on first run):**

   ```powershell
   lake build
   ```

   If you see “unknown import Mathlib”, ensure you opened the **project root** (the folder with `lakefile.toml`) and run `lake build`.

> Windows PATH tip: if `lake` is not found, add `%USERPROFILE%\.elan\bin` to your user PATH, then reopen your terminal.

### Option B — Online (quick check)

* Go to **[https://live.lean-lang.org/](https://live.lean-lang.org/)**
* Paste the relevant file contents to experiment interactively.
  (For a graded submission, a proper Lake project is preferred.)

---

## File layout

* **`Task1/Lean/Basic.lean`** — *Main file*: all sections (0/1/2) are here.
  The project’s top-level file (often `Lean.lean`) should import it:

  ```lean
  import Task1.Lean.Basic
  ```

* **Dependencies:** `Mathlib`, `Mathlib.Tactic`.

---

## Usage notes (tactics & patterns)

* **Rewriting / simplification:** `rw`, `simp`, `simpa`.
* **Arithmetic:**

  * `ring` for polynomial equalities (`k^2 + (2k+1) = (k+1)^2`)
  * `linarith`/`nlinarith` for (non)linear inequalities
  * `norm_num` for numeric goals
* **Conjunction / existence:**

  * `constructor` splits `A ∧ B`
  * `use c, n0` provides witnesses for `∃ c n0, …`
* **Nat ↔ Real casting:**
  When a hypothesis is on `ℕ` but the goal is on `ℝ`, cast it:

  ```lean
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  ```
* **Induction pattern (on `n : ℕ`):**

  ```lean
  induction n with
  | zero => simp [...]
  | succ k IH => simp [recDef, IH]; ring
  ```

---

## Asymptotic definitions used here

In this project we keep **simple** (no absolute values) and quantify over `n : ℕ`:

```lean
def isBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (n0 : ℕ), 0 < c ∧ ∀ ⦃n : ℕ⦄, n ≥ n0 → f n ≤ c * g n

def isBigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (n0 : ℕ), 0 < c ∧ ∀ ⦃n : ℕ⦄, n ≥ n0 → c * g n ≤ f n

def isBigTheta (f g : ℕ → ℝ) : Prop :=
  isBigOmega f g ∧ isBigO f g
```

> If you later want the **robust** variant (works for sign-changing functions), wrap both sides with `|·|`.

---

## What to submit

* **Lean project folder** that builds with `lake build`.
* **README.md** (this file).
* **Your `.lean` file(s)** with clear comments.
* **AI prompts disclosure** (if you used tools):
  add comment blocks like:

  ```lean
  -- Prompt: "Show 3n + 2 ∈ O(n) without absolute values."
  ```

  and keep a short list of prompts at the end of your `.lean` file or attach as an appendix.

---

## Points mapping (self-check)

* **Section 0 (4 pts):** basic equations/inequalities compile; no `sorry`.
* **Section 1 (5 pts):** O/Ω/Θ definitions + at least two small proofs (e.g., `2n+4 ∈ O(n)`, `3n+2 ∈ Θ(n)`).
* **Section 2 (3 pts):** recursive def + closed form (`sumNR` / `sumOdd`) and `fib` definition.

---

## Common pitfalls & quick fixes

* **Unknown `Mathlib`:** run `lake build` in the project root; ensure VS Code opened that folder.
* **`.olean` missing:** a file is imported but not built—run `lake build`; ensure the importing file is reachable via a top-level import.
* **`linarith` with Nat/Real:** cast Nat facts to Real via `exact_mod_cast`.
* **PATH issues (Windows):** add `%USERPROFILE%\.elan\bin` to PATH.

---

## License / Attribution

```
/- Copyright (c) Kelin Luo,
   2025. All rights reserved. -/
```

Lean proofs are original; standard tactics and definitions come from the open-source `mathlib`.

