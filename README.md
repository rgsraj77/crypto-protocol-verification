# Risk Analysis and Verification of Cryptographic Protocols
### MSc Project — guide to this submission

**Author:** Raj Guru Suwalka (250331929)
**Supervisor:** Dr Edon Kelmendi
**Programme:** MSc Data Science & Artificial Intelligence, Queen Mary University of London, 2025–26
**Module:** ECS750P / ECS753P / ECS754P — MSc Project

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
| `RajSuwalka_PG_Project_Dissertation.pdf` | Project summary report |
| `RajSuwalka_PG_Project_ReflectiveEssay.pdf` | Project reflective essay | 

---

## 3. Suggested order for the reader

The **report** is the full account and the best starting point. Within *this folder*:

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

## Interactive Web Tool
**Live App:** [Launch CryptoShield Web Tool](https://cryptoshield-web-tool.streamlit.app/)
