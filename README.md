# Risk Analysis and Verification of Cryptographic Protocols
### MSc Project — guide to this submission

**Author:** Raj Guru Suwalka (250331929)
**Supervisor:** Dr Edon Kelmendi
**Programme:** MSc Data Science & Artificial Intelligence, Queen Mary University of London, 2025–26
**Module:** ECS750P / ECS753P / ECS754P — MSc Project

---

## How this submission is organised

The project is submitted in **three parts**:

- **Part 1 — Report & reflective essay** *(submitted separately)*: the dissertation paper
  (`RajSuwalka_PG_Project_Dissertation.pdf`) and the reflective essay (`RajSuwalka_PG_Project_ReflectiveEssay.pdf`).
- **Part 2 — this supplementary-material folder**: the code, data, and machine-checked proofs.
- **Part 3 — the presentation video** *(submitted separately)* (`RajSuwalka_PG_Project_VideoPresentation`).

**This README guides you through Part 2.** Where the report and video are referred to below, they
are found in Parts 1 and 3.

---

## 1. What this project is

A two-stage pipeline for assessing cryptographic protocols:

1. An **empirical stage** learns to triage one hundred protocols by risk from their design
   features (a machine-learning classifier plus statistical validation).
2. A **formal-verification stage** produces machine-checked proofs, in **Lean 4**, of the
   attacks — or the safety — of the protocols the first stage flags as most concerning.

A small **bridge** joins the two, turning the model's ranking into an explicit, machine-readable
queue of protocols for the formal work. Every High-severity protocol identified by the model is
formalised in Lean.

---

## 2. Contents of this folder

| File | What it is |
|------|------------|
| `README.md` | This guide |
| `ProtocolsDolevYao.lean` | Shallow Dolev–Yao attack witnesses for the 13 High-severity protocols. **Annotated** — each protocol has a plain-language explanation of its flaw before the code |
| `ProtocolsPaulson.lean` | Paulson-style inductive (trace-level) proofs for 5 protocols |
| `SafeProtocols.lean` | Three certified safety results, each in a different proof style |
| `ChallengeResponseSafety.lean` | A full inductive safety proof over unbounded sessions |
| `WEPDemo.lean` | A standalone extract of the WEP proof used in the video demonstration (same proof as in `ProtocolsDolevYao.lean`) |
| `risk_analysis_consolidated.ipynb` | The empirical pipeline (Jupyter notebook) |
| `final_dv1.csv` | The curated 100-protocol dataset the notebook reads |
| `protocol_ranking.csv` | The ML→Lean handover — all 100 protocols ranked by composite vulnerability score, with a `lean_status` column (a pre-generated copy of the notebook's output) |
| `presentation_slides.pdf` | The slide deck from the presentation video (Part 3), included here for convenient reference |

The **report** and **reflective essay** (Part 1) and the **presentation video** (Part 3) are
submitted separately, not in this folder.

---

## 3. Suggested order for the reader

The **report** (Part 1) is the full account and the best starting point; the **video** (Part 3) is a
10-minute overview. Within *this folder*:

1. **`protocol_ranking.csv`** — the headline result at a glance: the top 13 rows are exactly the 13
   High-severity protocols.
2. **`risk_analysis_consolidated.ipynb`** — reproduces every empirical number in the paper.
3. **The Lean files** — the machine-checked proofs (Appendix A of the report inventories them).
   `WEPDemo.lean` is the smallest complete example to read first.

---

## 4. Reproducing the empirical results

**Requirements:** Python 3 with `pandas`, `numpy`, `scipy`, `scikit-learn`, `matplotlib`, and
Jupyter (any recent versions).

**Steps:**
1. Keep `final_dv1.csv` in the same folder as the notebook.
2. Open `risk_analysis_consolidated.ipynb` and run all cells.

All randomness is seeded (**seed = 42**), so a clean run regenerates every figure reported in the
paper and re-writes `protocol_ranking.csv` — the ranked handover that the formal stage consumes. A
pre-generated copy of that file is included in this folder, so you can inspect the ranking without
running the notebook.

---

## 5. Checking the Lean proofs

**Requirements:** **Lean 4** (developed and checked on `leanprover/lean4:v4.32.2`, the `stable`
channel) with the Lean 4 extension for VS Code. **No Mathlib and no other dependencies** — every file imports only the
Lean 4 core library, so each compiles on a stock Lean 4 install.

**To check:** open any `.lean` file in VS Code and let it elaborate. A file with no error markers
(no red underlines) means every proof in it has been verified by Lean. The five files are
independent and can be opened in any order.

**One expected warning.** `ProtocolsPaulson.lean` retains a deliberately *incomplete* first
attempt at the Woo-Lam attack trace, left as `sorry` and documented in place (see the note in the
`WooLam_Original` namespace). It records a modelling subtlety encountered during the project; the
Woo-Lam result itself is **proved completely** just below it, in the `WooLam_Original_Revised`
namespace. Lean will therefore print one `declaration uses 'sorry'` warning for this file — this is
expected and explained, not a gap in the results. All five Paulson results are complete and
machine-checked.

---

## 6. Where the paper's claims live

- **The ranking result** ("top thirteen = the thirteen High-severity protocols", §V) — the bridge
  stage of `risk_analysis_consolidated.ipynb` produces `protocol_ranking.csv` (included here); its
  top 13 rows are exactly the 13 High-severity protocols.
- **The end-to-end WEP worked example** (§VI) — `WEPDemo.lean`, and Part VIII of
  `ProtocolsDolevYao.lean`.
- **The formal-verification coverage** (Appendix A) — the five Lean files listed above.
