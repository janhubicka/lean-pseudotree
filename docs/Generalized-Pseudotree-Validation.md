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

## Audited whole-block extension checkpoint

Actions run 45866695059, job 140071239421, passed the independent CriticalExtensionBase audit at db3a8b7db01053e1f233ef89d1e890daf80c3a00: 4314 declarations use only propext, Classical.choice and Quot.sound. The core build also passed. This checkpoint adds the unchanged audited source blobs for RelativeSlots (including the actual A.3(1) whole-block extension theorem), NextBlockMilliken, SlotSuffixMaps, DiaryRestriction and their aggregate import. It includes the meet-closed-to-arbitrary-labelled-diary restriction bridge. The subsequent full branch build compiled CodingCover and SlotTransport, but those modules were not part of this independent audit. The remaining A.3(2), A.4 and expanded-copy reconstruction endpoints remain on the validation branch. The main workflow is unchanged.

## Audited local pigeonhole checkpoint

Actions run 45868929249, job 140078951502, at e0800b70dede66dc93e116c5c5171426df1d668a passed the LocalPigeonholeBase audit of 4470 declarations (only propext, Classical.choice and Quot.sound). This checkpoint adds exactly the audited source blobs of CodingCover, RelativeReservoirInit, SlotTransport, LocalPigeonhole and their aggregate. It includes the finite coding witnesses, relative initial layer, exact FIFO composition, and local A.4 homogeneous refinement for the empty and nonempty prefix. The full branch build also compiled the infinite relative reservoir continuation, labelled reconstruction, label recovery and native first-order expansion, but those were outside the independent audit. The A.3(2) and ambient A.4 endpoints and the full expanded-copy identification remain on the validation branch. Main workflow unchanged; manuscript PDF verification is manual.

## Audited reconstruction checkpoint

Actions run 45870721374 at 5590db2535622c4e26055ba1cb493d1c027f897f, job 140085123309, completed the independent ReconstructionBase build and transitive audit successfully (steps 5–6). The exact unchanged audited source blobs are promoted here. This includes the infinite relative reservoir continuation, critical-map reconstruction from all labelled finite coding relations, label recovery from the length order and meet-closed diary relations, and the native first-order expansion with preservation/reflection by critical embeddings and labelled preservation by native embeddings. The full branch build of A.3(2), ambient A.4, range identification and analytic transfer was still in progress at promotion; no claim about those endpoints is made here. Main workflow unchanged. Manuscript PDF verification is manual.
