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

## Audited relative geometry checkpoint

The independently compiled and transitively audited CriticalGeometryBase at 08ad7fb47ef224e74f1a788a0e2148822ceb3219 passed steps 7–8 of Actions run 45863816431 (job 140061409213). All 4126 declarations in the pseudotree namespace use only propext, Classical.choice and Quot.sound. The core build also passed. This checkpoint promotes exactly those imported relative-geometry modules, preserving their source blobs unchanged and retaining the main workflow. It includes strict A.2, depth, critical-copy pullback, relative FIFO local geometry and prefix/tail gluing, coding-range support and inclusion, the conditional A.3(2) range reduction, rational slot reservoirs, and relative restricted Milliken. It does not claim the complete A.3(1), A.3(2), A.4, reconstruction or topology endpoints; these remain on the validation branch. A.3(1) and next-block Milliken compiled in the subsequent full-build step, but were outside the independent transitive audit.
