(*  Title:      AutoCorrode/Enum_Theory/Enum_Tests.thy
    Author:     AutoCorrode Project

    Comprehensive test suite for the enum command.
    This file is not included in ROOT - it's for manual testing.
*)

theory Enum_Tests
imports Enum_Theory
begin

section \<open>Simple Enums (Nullary Constructors Only)\<close>

subsection \<open>Basic Simple Enum\<close>

enum color = Red | Green | Blue

text \<open>Check generated constructors\<close>
term "color.Red"
term "color.Green"
term "color.Blue"

text \<open>Check generated case combinator\<close>
term "color.case"
thm color.case_def
thm color.distinct
thm color.exhaust

text \<open>Check case equality theorems\<close>
thm color.cases

text \<open>Check induction principle\<close>
thm color.induct

subsection \<open>Using Induction\<close>

lemma color_exhaustive: "c = Red \<or> c = Green \<or> c = Blue"
  by (induction c) auto

lemma color_case_tac_test: "c = Red \<or> c = Green \<or> c = Blue"
  apply (case_tac c)
  by auto

subsection \<open>Using Case Expression\<close>

definition color_to_nat :: "color \<Rightarrow> nat" where
  "color_to_nat c = (case c of Red \<Rightarrow> 1 | Green \<Rightarrow> 2 | Blue \<Rightarrow> 3)"

lemma color_to_nat_Red: "color_to_nat Red = 1"
  by (simp add: color_to_nat_def)

lemma color_to_nat_Green: "color_to_nat Green = 2"
  by (simp add: color_to_nat_def)

lemma color_to_nat_Blue: "color_to_nat Blue = 3"
  by (simp add: color_to_nat_def)

subsection \<open>Single Constructor Enum\<close>

enum unit_like = Unit

thm unit_like.induct
thm unit_like.cases

lemma unit_like_unique: "x = Unit"
  by (induction x rule: unit_like.induct) auto

subsection \<open>Two Constructor Enum\<close>

enum binary = Zero | One

thm binary.induct
thm binary.cases

definition binary_not :: "binary \<Rightarrow> binary" where
  "binary_not b = (case b of Zero \<Rightarrow> One | One \<Rightarrow> Zero)"

lemma binary_not_involutive: "binary_not (binary_not b) = b"
  by (induction b rule: binary.induct) (auto simp: binary_not_def)

subsection \<open>Many Constructor Enum\<close>

enum day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday

thm day.induct
thm day.cases

definition is_weekend :: "day \<Rightarrow> bool" where
  "is_weekend d = (case d of
    Monday \<Rightarrow> False
  | Tuesday \<Rightarrow> False
  | Wednesday \<Rightarrow> False
  | Thursday \<Rightarrow> False
  | Friday \<Rightarrow> False
  | Saturday \<Rightarrow> True
  | Sunday \<Rightarrow> True)"

lemma weekend_or_weekday: "is_weekend d \<or> \<not>is_weekend d"
  by auto

section \<open>Complex Enums (Constructors with Arguments)\<close>

subsection \<open>Option-like Type\<close>

enum option_nat = None1 | Some1 nat

text \<open>Check generated constructors\<close>
term "option_nat.None1"
term "option_nat.Some1"

text \<open>Check constructor types\<close>
term "option_nat.Some1 :: nat \<Rightarrow> option_nat"

text \<open>Check case combinator\<close>
term "option_nat.case"
thm option_nat.case_def

text \<open>Check theorems\<close>
thm option_nat.induct
thm option_nat.exhaust
thm option_nat.cases
thm option_nat.is_enum

subsection \<open>Using Complex Enum\<close>

definition option_nat_default :: "option_nat \<Rightarrow> nat \<Rightarrow> nat" where
  "option_nat_default x d = (case x of None1 \<Rightarrow> d | Some1 n \<Rightarrow> n)"

lemma option_nat_default_None: "option_nat_default None1 d = d"
  by (simp add: option_nat_default_def)

lemma option_nat_default_Some: "option_nat_default (Some1 n) d = n"
  by (simp add: option_nat_default_def)

subsection \<open>Result Type (Three Constructors)\<close>

enum result = Success nat | Failure string | Pending

thm result.induct
thm result.cases
thm result.is_enum

lemma \<open>Success x \<noteq> Failure y\<close>
  by simp

definition is_success :: "result \<Rightarrow> bool" where
  "is_success r = (case r of Success _ \<Rightarrow> True | Failure _ \<Rightarrow> False | Pending \<Rightarrow> False)"

definition is_failure :: "result \<Rightarrow> bool" where
  "is_failure r = (case r of Success _ \<Rightarrow> False | Failure _ \<Rightarrow> True | Pending \<Rightarrow> False)"

definition is_pending :: "result \<Rightarrow> bool" where
  "is_pending r = (case r of Success _ \<Rightarrow> False | Failure _ \<Rightarrow> False | Pending \<Rightarrow> True)"

lemma result_classification: "is_success r \<or> is_failure r \<or> is_pending r"
  by (induction r rule: result.induct)
     (auto simp: is_success_def is_failure_def is_pending_def)

subsection \<open>Multiple Arguments\<close>

enum pair_nat_bool = Pair nat bool

thm pair_nat_bool.induct
thm pair_nat_bool.cases
thm pair_nat_bool.is_enum

definition fst_pair :: "pair_nat_bool \<Rightarrow> nat" where
  "fst_pair p = (case p of Pair n _ \<Rightarrow> n)"

definition snd_pair :: "pair_nat_bool \<Rightarrow> bool" where
  "snd_pair p = (case p of Pair _ b \<Rightarrow> b)"

lemma pair_split: "p = Pair (fst_pair p) (snd_pair p)"
  by (induction p rule: pair_nat_bool.induct)
     (auto simp: fst_pair_def snd_pair_def)

subsection \<open>Mixed Constructors\<close>

enum mixed = Nullary | Unary nat | Binary nat bool | Ternary nat bool string

thm mixed.induct
thm mixed.cases
thm mixed.is_enum

definition mixed_count_args :: "mixed \<Rightarrow> nat" where
  "mixed_count_args m = (case m of
    Nullary \<Rightarrow> 0
  | Unary _ \<Rightarrow> 1
  | Binary _ _ \<Rightarrow> 2
  | Ternary _ _ _ \<Rightarrow> 3)"

lemma mixed_count_bound: "mixed_count_args m \<le> 3"
  by (induction m rule: mixed.induct) (auto simp: mixed_count_args_def)

section \<open>Stress Tests\<close>

subsection \<open>Many Simple Constructors\<close>

enum alphabet =
  A | B | C | D | E | F | G | H | I | J | K | L | M |
  N | O | P | Q | R | S | T | U | V | W | X | Y | Z

thm alphabet.Abs_inverse
thm alphabet.case_def
thm alphabet.induct
thm alphabet.cases
thm alphabet.exhaust
thm alphabet.distinct

lemma alphabet_cases_test:
  fixes x :: alphabet
  shows "x = A \<or> x = B \<or> x = C \<or> x = D \<or> x = E \<or> x = F \<or> x = G \<or>
         x = H \<or> x = I \<or> x = J \<or> x = K \<or> x = L \<or> x = M \<or>
         x = N \<or> x = alphabet.O \<or> x = P \<or> x = Q \<or> x = R \<or> x = S \<or>
         x = T \<or> x = U \<or> x = V \<or> x = W \<or> x = X \<or> x = Y \<or> x = Z"
  apply (cases x)
  by auto

lemma \<open>A \<noteq> Z\<close>
  apply simp
  done

subsection \<open>Complex Types as Arguments\<close>

enum nested = Leaf | Node "nat list" | Branch "nat \<Rightarrow> bool"

thm nested.induct
thm nested.cases

definition has_list :: "nested \<Rightarrow> bool" where
  "has_list n = (case n of Leaf \<Rightarrow> False | Node _ \<Rightarrow> True | Branch _ \<Rightarrow> False)"

section \<open>Pattern Matching Examples\<close>

subsection \<open>Nested Pattern Matching\<close>

definition color_result :: "result \<Rightarrow> color" where
  "color_result r = (case r of
    Success n \<Rightarrow> (if n = 0 then Red else if n = 1 then Green else Blue)
  | Failure _ \<Rightarrow> Red
  | Pending \<Rightarrow> Blue)"

subsection \<open>Higher-Order Functions\<close>

definition map_result :: "(nat \<Rightarrow> nat) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> result \<Rightarrow> result" where
  "map_result f g r = (case r of
    Success n \<Rightarrow> Success (f n)
  | Failure s \<Rightarrow> Failure (g s)
  | Pending \<Rightarrow> Pending)"

lemma map_result_Success: "map_result f g (Success n) = Success (f n)"
  by (simp add: map_result_def)

lemma map_result_Pending: "map_result f g Pending = Pending"
  by (simp add: map_result_def)

section \<open>Induction Proof Examples\<close>

subsection \<open>Simple Induction\<close>

definition all_colors :: "color list" where
  "all_colors = [Red, Green, Blue]"

lemma color_in_all_colors: "c \<in> set all_colors"
  by (induction c rule: color.induct) (auto simp: all_colors_def)

subsection \<open>Complex Induction\<close>

definition result_to_option :: "result \<Rightarrow> nat option" where
  "result_to_option r = (case r of Success n \<Rightarrow> Some n | _ \<Rightarrow> None)"

section \<open>Integration with Standard Isabelle Types\<close>

subsection \<open>Lists\<close>

definition result_list_filter :: "result list \<Rightarrow> nat list" where
  "result_list_filter rs \<equiv> map (\<lambda>r. case r of Success n \<Rightarrow> n | _ \<Rightarrow> 0) rs"

subsection \<open>Options\<close>

definition result_to_std_option :: "result \<Rightarrow> nat option" where
  "result_to_std_option r \<equiv> (case r of Success n \<Rightarrow> Some n | _ \<Rightarrow> None)"

text \<open>
  All tests passed! The enum command successfully:
  - Generates types via typedef
  - Creates qualified constructors
  - Produces induction principles
  - Defines case combinators
  - Proves case equality theorems
  - Integrates with pattern matching
  - Handles both simple and complex enums
  - Supports arbitrary argument types
  - Works with standard Isabelle reasoning
\<close>

section \<open>Named Case Tests\<close>

subsection \<open>Cases\<close>

lemma binary_cases_named:
  shows \<open>b = Zero \<or> b = One\<close>
proof (cases b)
  case Zero
  then show ?thesis by simp
next
  case One
  then show ?thesis by simp
qed

lemma color_cases_named:
  shows \<open>color_to_nat c > 0\<close>
proof (cases c)
  case Red
  then show ?thesis by (simp add: color_to_nat_def)
next
  case Green
  then show ?thesis by (simp add: color_to_nat_def)
next
  case Blue
  then show ?thesis by (simp add: color_to_nat_def)
qed

lemma option_nat_cases_named:
  shows \<open>x = None1 \<or> (\<exists>n. x = Some1 n)\<close>
proof (cases x)
  case None1
  then show ?thesis by simp
next
  case (Some1 n)
  then show ?thesis by blast
qed

subsection \<open>Induction\<close>

lemma binary_induct_named:
  shows \<open>b = Zero \<or> b = One\<close>
proof (induction b)
  case Zero
  then show ?case by simp
next
  case One
  then show ?case by simp
qed

lemma color_induct_named:
  shows \<open>color_to_nat c > 0\<close>
proof (induction c)
  case Red
  then show ?case by (simp add: color_to_nat_def)
next
  case Green
  then show ?case by (simp add: color_to_nat_def)
next
  case Blue
  then show ?case by (simp add: color_to_nat_def)
qed

lemma option_nat_induct_named:
  shows \<open>x = None1 \<or> (\<exists>n. x = Some1 n)\<close>
proof (induction x)
  case None1
  then show ?case by simp
next
  case (Some1 n)
  then show ?case by blast
qed

section \<open>Code Generation Tests\<close>

value \<open>color_to_nat Blue\<close>
value \<open>is_weekend Saturday\<close>
value \<open>option_nat_default (Some1 42) 0\<close>
value \<open>Red = Green\<close>
value \<open>Green = Red\<close>
value \<open>Red = Red\<close>
value \<open>Monday = Sunday\<close>
value \<open>is_success (Success 5)\<close>


end
