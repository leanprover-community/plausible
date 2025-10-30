import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.BinaryTree

open DecOpt

set_option guard_msgs.diff true

#guard_msgs(drop info, drop warning) in
derive_checker (fun lo x hi => Between lo x hi)

#guard_msgs(drop info, drop warning) in
derive_checker (fun lo hi t => BST lo hi t)
