"""Deformalization 3: descent to a layer of the cyclotomic tower. Read by scripts/build_digest.py.

The note treats a whole unit of the archive (cyclotomic layers and twisted Galois actions): the actions on the
module of characters and their twists, roots of unity and levels, generators, the invariants under a generator
(Input 2b of the first note) and the descent of the locally trivial classes over a layer (Input 2a)."""

AV = "Development/AutomorphicArithmetic/AutomorphicVarieties/"
NT = AV + "NumberFieldTowers/"
K = AV + "GaloisLibrary/KummerTheory/"
ST = AV + "GaloisLibrary/SelmerTransport/"
CL = AV + "GaloisLibrary/GaloisCohomologyLength/"
X = NT + "XTwApplyApply.lean"
DIRECTORY = NT

# key, name shown, file, word that opens the declaration, name as written at its head
DECLS = [
    # actions, twists, invariants and the small definitions (members of the unit)
    ("dRep", "Tower.dRep", X, "def", "dRep"),
    ("xRep", "Tower.xRep", X, "def", "xRep"),
    ("xRepApply", "Tower.xRep_apply", X, "theorem", "xRep_apply"),
    ("twist", "Tower.twist", X, "def", "twist"),
    ("dTw", "Tower.dTw", X, "def", "dTw"),
    ("xTw", "Tower.xTw", X, "def", "xTw"),
    ("dTwApply", "Tower.dTw_apply", X, "theorem", "dTw_apply"),
    ("xTwApply", "Tower.xTw_apply", X, "theorem", "xTw_apply"),
    ("xTwApplyApply", "Tower.xTw_apply_apply", X, "theorem", "xTw_apply_apply"),
    ("ShaD", "Tower.ShaD", X, "abbrev", "ShaD"),
    ("IsGen", "Tower.IsGen", X, "def", "IsGen"),
    ("cZero", "Tower.cZero", X, "def", "cZero"),
    ("layU", "Tower.layU", X, "abbrev", "layU"),
    ("layF", "Tower.layF", X, "abbrev", "layF"),
    ("XN", "Tower.XN", X, "abbrev", "XN"),
    ("XX", "Tower.XX", X, "abbrev", "XX"),
    ("XP", "Tower.XP", X, "abbrev", "XP"),
    ("GenLE", "Tower.GenLE", X, "def", "GenLE"),
    ("GenLEfinite", "Tower.GenLE.finite", X, "theorem", "GenLE.finite"),
    ("cokerLen", "Tower.cokerLen", X, "def", "cokerLen"),
    ("xRank", "Tower.xRank", X, "def", "xRank"),
    ("IsTower", "Tower.IsTower", X, "structure", "IsTower"),
    ("IsDesc", "Tower.IsDesc", NT + "IdealNormClassCongr.lean", "def", "IsDesc"),
    # roots of unity and levels
    ("cycMemPrinc", "cyc_mem_princ_iff", NT + "CycMemPrincIff.lean", "private theorem", "cyc_mem_princ_iff"),
    ("leFinrank", "le_finrank", NT + "CycMemPrincIff.lean", "private theorem", "le_finrank"),
    ("exIff", "ex_iff", NT + "CycMemPrincIff.lean", "private theorem", "ex_iff"),
    ("allIff", "all_iff", NT + "CycMemPrincIff.lean", "private theorem", "all_iff"),
    ("muQ", "Tower.muQ", NT + "CycMemPrincIff.lean", "theorem", "UpperTheory.V.Tower.muQ"),
    # torsion, generators, invariants
    ("dinfTors", "Tower.dinfTors", NT + "DinfTors.lean", "theorem", "UpperTheory.V.Tower.dinfTors"),
    ("existsGen", "Tower.existsGen", NT + "ExistsGen.lean", "theorem", "UpperTheory.V.Tower.existsGen"),
    ("genGal", "Tower.genGal", NT + "GenGal.lean", "theorem", "UpperTheory.V.Tower.genGal"),
    ("shaDGen", "Tower.shaDGen", NT + "ShaDGen.lean", "theorem", "UpperTheory.V.Tower.shaDGen"),
    # transport and descent
    ("dtVal", "dt_val_lt_one", NT + "DinfTransport.lean", "private theorem", "dt_val_lt_one"),
    ("dtDec", "dt_dec", NT + "DinfTransport.lean", "private theorem", "dt_dec"),
    ("dtIne", "dt_ine", NT + "DinfTransport.lean", "private theorem", "dt_ine"),
    ("dtMem", "dt_mem", NT + "DinfTransport.lean", "private theorem", "dt_mem"),
    ("dinfTransport", "Tower.dinfTransport", NT + "DinfTransport.lean", "theorem", "UpperTheory.V.Tower.dinfTransport"),
    ("desc", "Tower.desc", NT + "Imports.lean", "theorem", "UpperTheory.V.Tower.desc"),
    # the separation lemma
    ("qzAnn", "exists_qz_ne_zero_annihilators_of_ne_zero", NT + "QzSep.lean", "private theorem",
     "exists_qz_ne_zero_annihilators_of_ne_zero"),
    # what the statements use from outside the unit
    ("G", "G", "Formalism/ConjugateSelfDual/Statement.lean", "abbrev", "G"),
    ("QZ", "QZ", "Formalism/GaloisCohomology/Statement.lean", "def", "QZ"),
    ("LData", "LData", "Formalism/GaloisCohomology/Statement.lean", "structure", "LData"),
    ("qzTw", "qzTw", "Formalism/GaloisCohomology/Statement.lean", "def", "qzTw"),
    ("Sha", "Sha", "Formalism/GaloisCohomology/Statement.lean", "def", "Sha"),
    ("cycZ", "Gal.cycZ", "ReciprocityTheory/GaloisValuations/Global.lean", "def", "cycZ"),
    ("princ", "princ", "Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/LeNuIffPowMemPrinc.lean",
     "noncomputable def", "princ"),
    ("levU", "Base.levU", ST + "ConjStableShaFam.lean", "def", "levU"),
    ("cycU", "Base.cycU", ST + "ConjStableShaFam.lean", "def", "cycU"),
    ("qExp", "Base.qExp", ST + "ConjStableShaFam.lean", "def", "qExp"),
    ("gamU", "Base.gamU", ST + "ConjStableShaFam.lean", "abbrev", "gamU"),
    ("galOf", "Base.galOf", ST + "ConjStableShaFam.lean", "def", "galOf"),
    ("galEmb", "Base.galEmb", ST + "ConjStableShaFam.lean", "def", "galEmb"),
    ("galEmbFam", "Base.galEmbFam", ST + "GalEmbFam.lean", "theorem", "UpperTheory.V.Base.galEmbFam"),
    ("galEmbTop", "Base.galEmbTop", ST + "GalEmbTop.lean", "theorem", "UpperTheory.V.Base.galEmbTop"),
    ("Dinf", "Kum.Dinf", K + "Mk0IdMapCongr.lean", "abbrev", "Dinf"),
    ("Xinf", "Kum.Xinf", K + "Mk0IdMapCongr.lean", "abbrev", "Xinf"),
    ("funRep", "Kum.funRep", K + "Mk0IdMapCongr.lean", "def", "funRep"),
    ("EqHom", "Kum.EqHom", K + "Mk0IdMapCongr.lean", "def", "EqHom"),
    ("Un", "Kum.Un", K + "Mk0IdMapCongr.lean", "abbrev", "Un"),
    ("Procyc", "Kum.Procyc", K + "Mk0IdMapCongr.lean", "def", "Procyc"),
    ("resInf", "Kum.resInf", K + "Mk0IdMapCongr.lean", "def", "resInf"),
    ("funRepMem", "Kum.funRepMem", K + "FunRepMem.lean", "theorem", "UpperTheory.V.Kum.funRepMem"),
    ("dinfNil", "Kum.dinfNil", K + "DinfNil.lean", "theorem", "UpperTheory.V.Kum.dinfNil"),
    ("kumExistsGen", "Kum.existsGen", K + "ExistsGen.lean", "theorem", "UpperTheory.V.Kum.existsGen"),
    ("resInfInj", "Kum.resInfInj", K + "ResInfInj.lean", "theorem", "UpperTheory.V.Kum.resInfInj"),
    ("resInfOnto", "Kum.resInfOnto", K + "ResInfOnto.lean", "theorem", "UpperTheory.V.Kum.resInfOnto"),
    ("zmodToQZ", "Kum.zmodToQZ", K + "ZmodToQZ.lean", "theorem", "UpperTheory.V.Kum.zmodToQZ"),
    ("HasMuQ", "HasMuQ", AV + "GeneratorCountTuples/LemmaK.lean", "def", "HasMuQ"),
    ("qzG", "qzG", CL + "LevelInertiaLeLevelDec.lean", "def", "qzG"),
    ("galTransport", "galTransport", CL + "GalTransport.lean", "theorem", "UpperTheory.V.LDataCardLeFinrank.galTransport"),
]
QUOTED = ["desc", "shaDGen", "muQ"]                        # statements printed in the appendix
LETTERED = [("Theorem A", "t:A"), ("Theorem B", "t:B"), ("Input G", "i:G"), ("Input R1", "i:R1"), ("Input R2", "i:R2")]

# the outline of the chapter
OUTLINE = [
    ("setting", "Actions and twists", "conjugation on the characters, its dual, twists by the cyclotomic character, invariants",
     ["dRep", "xRep", "xRepApply", "twist", "dTw", "xTw", "dTwApply", "xTwApply", "xTwApplyApply", "ShaD", "IsGen",
      "cZero", "layU", "layF", "XN", "XX", "XP", "GenLE", "GenLEfinite", "cokerLen", "xRank", "IsTower", "IsDesc"]),
    ("roots", "Roots of unity and levels", "which roots of unity of l-power order a number field contains, read on the cyclotomic character",
     ["cycMemPrinc", "leFinrank", "exIff", "allIff", "muQ"]),
    ("torsion", "Torsion and trivial action", "characters have l-power order; the kernel of the cyclotomic character acts trivially",
     ["dinfTors"]),
    ("generators", "Generators", "a closed subgroup has an element whose cyclotomic value generates its image topologically",
     ["existsGen", "genGal"]),
    ("invariants", "Theorem B", "the invariants of a subgroup under a twisted action are the fixed points of one generator",
     ["shaDGen"]),
    ("transport", "Transport of characters", "an isomorphism of algebraic closures carries the module of characters along",
     ["dtVal", "dtDec", "dtIne", "dtMem", "dinfTransport"]),
    ("descent", "Theorem A", "restriction identifies the locally trivial classes over a layer with twisted invariants",
     ["desc"]),
    ("separation", "A separation lemma", "a nonzero element of a module over the l-adic integers is detected by a character",
     ["qzAnn"]),
]
