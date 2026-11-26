# Verified generalized pseudotree checkpoint

The source of this checkpoint is the independently audited generalized base
at b15c8368a1a257313eaec2aedbda698b1c843277, GitHub Actions run 45845706438, job 139998677723, steps 5–6.
The core build also passed (run 45845706560).

The exact generalized-base sources passed compilation and transitive axiom
audit of 3841 declarations in the pseudotree namespace. Only propext,
Classical.choice and Quot.sound were found. This includes generalized
normalization, literal grammar/extraction/recovery, absolute FIFO lifting,
finite-fragment canonization and code-set IRT, infinite recurrence in any
sparse reduct copy, and the concrete A.1, A.2 and metric closedness interface.
The first-order expansion packaging, digit-convention transport, concrete
A.3/A.4 and identification with expanded self-copies are not verified here.

This checkpoint retains the audited sources unchanged; only the aggregate
import, audit entry point, documentation and workflow selection differ from
the audited branch. Unfinished relative modules are retained on
critical-copy-space-validation, not included in the main library. The
full branch run had failed after the successful generalized audit.
