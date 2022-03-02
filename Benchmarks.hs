import qualified Data.Map as Map
import qualified Data.List as List
import Numeric (showFFloat)

results =
  Map.fromList
    [ ("prop_01", (0.75466996, 0.23165)),
      ("prop_06", (0.23989001, 8.082001e-2)),
      ("prop_07", (0.3444, 0.14812)),
      ("prop_08", (0.26927, 9.0900004e-2)),
      ("prop_09", (0.92449987, 0.47647)),
      ("prop_10", (0.26254997, 0.17208001)),
      ("prop_11", (2.0289999e-2, 1.01e-3)),
      ("prop_12", (1.2254, 0.45782)),
      ("prop_13", (4.9870003e-2, 2.1800003e-3)),
      ("prop_17", (0.19893, 6.25e-3)),
      ("prop_18", (0.25219, 7.749999e-2)),
      ("prop_19", (1.17257, 0.5777)),
      ("prop_21", (0.21182, 7.173e-2)),
      ("prop_22", (2.0517402, 0.99556)),
      ("prop_23", (1.1794201, 0.68483)),
      ("prop_24", (1.1966398, 0.53101003)),
      ("prop_25", (1.33154, 0.83787)),
      ("prop_31", (2.05133, 1.0301499)),
      ("prop_32", (0.97365, 0.29411)),
      ("prop_33", (0.45864, 0.17883)),
      ("prop_34", (0.83159, 0.25836998)),
      ("prop_35", (0.31330997, 5.5e-3)),
      ("prop_36", (0.19318, 6.954e-2)),
      ("prop_40", (1.374e-2, 8.3e-4)),
      ("prop_41", (1.04773, 0.45659)),
      ("prop_42", (5.9989996e-2, 2.5799996e-3)),
      ("prop_44", (0.21817999, 1.172e-2)),
      ("prop_45", (9.3669996e-2, 3.8699997e-3)),
      ("prop_46", (3.4560002e-2, 1.2e-3)),
      ("prop_49", (556.56, 537.036)),
      ("prop_50", (23.47023, 20.32431)),
      ("prop_51", (3.6449802, 2.1346302)),
      ("prop_55", (1.8156201, 0.65824)),
      ("prop_56", (41281.195, 39820.926)),
      ("prop_57", (3.7718704, 2.7090201)),
      ("prop_58", (5.13764, 3.3614101)),
      ("prop_61", (427.09238, 376.6517)),
      ("prop_64", (1.3620999, 0.83595)),
      ("prop_67", (1.71219, 0.72237)),
      ("prop_79", (317.9885, 298.21927)),
      ("prop_80", (1.3532299, 0.48976)),
      ("prop_82", (2.9808898, 2.06213)),
      ("prop_83", (3.04563, 1.64236)),
      ("prop_84", (3.56652, 1.27708))
    ]

-- | Convert benchmark to latex tabular
showMark :: Map.Map String (Double, Double) -> String
showMark bm =
  unlines $ pre ++ titles : Map.foldrWithKey (\k v ss -> entry k v : ss) post bm
  where
    pre = ["\\begin{tabular}{llll}", "\\toprule"]
    titles = concat $ List.intersperse " & " ["Name", "Total Time (ms)", "Edge Time (ms)", "Edge Time (\\%)"] ++ ["\\\\\\midrule"]
    post = ["\\bottomrule", "\\end{tabular}"]

    -- Format an entry
    entry n (total, edge) =
      let percent = 100 * (edge / total) 
       in 
      concat $
        List.intersperse
          " & "
          [n, showFFloat (Just 2) total "", showFFloat (Just 2) edge "", showFFloat (Just 2) percent ""]
          ++ ["\\\\\\midrule"]
