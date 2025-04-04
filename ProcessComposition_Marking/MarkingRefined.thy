theory MarkingRefined
  imports
    MarkingAbstract
begin

section\<open>Refined Model of Marking\<close>

text\<open>
  In the refined view we know the range of students submitting the assignment.
  For each of the students we can get their name for the purpose of labelling the actions.
\<close>
locale refined =
  fixes students :: "'s list"
    and name :: "'s \<Rightarrow> String.literal"
begin

text\<open>
  Linear resources are individual students, submissions, marks and their status.
  This is parameterised by the type of students.
\<close>
datatype 'a lres = Student 'a \<comment> \<open>Individual student\<close>
  | Submission 'a \<comment> \<open>Individual student's submission\<close>
  | Mark 'a \<comment> \<open>Individual student's mark\<close>
  | MarkSubmitted 'a \<comment> \<open>Individual student's mark has been submitted\<close>
  | MarksReleased \<comment> \<open>All marks have been released\<close>

text\<open>Copyable resources are the same as in the abstract view: the instructions\<close>
type_alias cres = abstract.cres
abbreviation "Instructions \<equiv> abstract.Instructions"

text\<open>Processes in this context use the above linear and copyable resources, and string labels\<close>
type_synonym 'a proc = "('a lres, cres, String.literal, unit) process"

subsection\<open>Resource Refinement\<close>

text\<open>
  We can turn all abstract linear resource atoms into refined resources by unfolding students,
  submissions, marks and their status into parallel combinations over the list of students
\<close>
primrec refinement :: "abstract.lres \<Rightarrow> ('s refined.lres, cres) resource"
  where
    "refinement abstract.Students = Parallel (map (Res \<circ> refined.Student) students)"
  | "refinement abstract.Submissions = Parallel (map (Res \<circ> refined.Submission) students)"
  | "refinement abstract.Marks = Parallel (map (Res \<circ> refined.Mark) students)"
  | "refinement abstract.MarksSubmitted = Parallel (map (Res \<circ> refined.MarkSubmitted) students)"
  | "refinement abstract.MarksReleased = Res refined.MarksReleased"

text\<open>Applying this refinement to the abstract marking process remains valid\<close>
lemma markingProcess_refined:
  defines [simp]: "x \<equiv> process_refineRes refinement id abstract.markingProcess"
    shows "valid x"
      and "input x = Copyable Instructions \<odot> Parallel (map (Resource.Res \<circ> Student) students)"
      and "output x = Res MarksReleased"
  by (simp_all add: abstract.markingProcess_def abstract.releaseMarks_def abstract.submitMarks_def
      abstract.markAll_def abstract.collectSubs_def refine_resource_par)

subsection\<open>Refined Collection of Submissions\<close>

text\<open>
  We can refine the monolithic actions collecting all students' submissions at once into a
  composition of several actions collecting each individual submission.
  The difficult part in this, apart from the substitution itself, is getting a copy of the
  instructions to each of the students.
  We define (and verify) helper functions to copy and swap that copyable atom appropriately.
\<close>

text\<open>There is an action to collect an individual submission\<close>
definition "collectStudent s =
  Primitive (Copyable Instructions \<odot> Res (Student s)) (Res (Submission s))
            (STR ''Collect submission of '' + name s) ()"

context
  includes process_notation
begin

text\<open>
  Given two lists of resources, we can compose a process to interleave them using swaps.
  We do this by recursion on the lists, swapping the tail of the first after the head of the second.
\<close>
fun swapInterleave :: "('a, 'b) resource list \<Rightarrow> ('a, 'b) resource list \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where
    "swapInterleave (x # xs) (y # ys) =
      Identity x \<parallel> Swap (Parallel xs) y \<parallel> Identity (Parallel ys) ;;
      Identity (x \<odot> y) \<parallel> swapInterleave xs ys"
  | "swapInterleave [] ys = Identity (Parallel ys)"
  | "swapInterleave xs [] = Identity (Parallel xs)"

lemma swapInterlave [simp]:
  fixes xs ys :: "('a, 'b) resource list"
  shows "input (swapInterleave xs ys) = Parallel (xs @ ys)"
    and "output (swapInterleave xs ys) = Parallel (splice xs ys)"
    and "valid (swapInterleave xs ys)"
proof -
  have [simp]:"input (swapInterleave xs ys) = Parallel (xs @ ys)"
    for xs ys :: "('a, 'b) resource list"
    by (induct xs ys rule: swapInterleave.induct ; simp)
  then show "input (swapInterleave xs ys) = Parallel (xs @ ys)" .

  show "output (swapInterleave xs ys) = Parallel (splice xs ys)"
    by (induct xs ys rule: swapInterleave.induct ; simp)
  show "valid (swapInterleave xs ys)"
    by (induct xs ys rule: swapInterleave.induct ; simp)
qed

text\<open>
  Given a number and a copyable atom, we can compose a process that replicates that atom the given
  number of times (or erases it if we want zero copies).
  We do this by recursion on the number of copies, with a base case at one instead of zero to avoid
  any unnecessary duplication followed by erasing.
\<close>
fun duplicateToN :: "nat \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'l, 'm) process"
  where
    "duplicateToN (Suc 0) r = Identity (Copyable r)"
  | "duplicateToN (Suc n) r = Duplicate r ;; Identity (Copyable r) \<parallel> duplicateToN n r"
  | "duplicateToN 0 r = Erase r"

lemma duplicateToN [simp]:
  fixes r :: 'b
  shows "input (duplicateToN n r) = Copyable r"
    and "output (duplicateToN n r) = nresource n (Copyable r)"
    and "valid (duplicateToN n r)"
proof -
  have [simp]: "input (duplicateToN n r) = Copyable r"
    for n and r :: 'b
    by (induct n r rule: duplicateToN.induct ; simp)
  then show "input (duplicateToN n r) = Copyable r" .

  show "output (duplicateToN n r) = nresource n (Copyable r)"
    by (induct n r rule: duplicateToN.induct ; simp add: nresource_simp)
  show "valid (duplicateToN n r)"
    by (induct n r rule: duplicateToN.induct ; simp)
qed

text\<open>
  Target condition for the action to replace uses its input and output, since those are required for
  the replacement to preserve validity (and in this case they also uniquely identify the action).
\<close>
definition collectionSplit_cond
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> bool"
  where "collectionSplit_cond a b l m = (
  a = Copyable Instructions \<odot> Parallel (map (Res \<circ> refined.Student) students) \<and>
  b = Parallel (map (Res \<circ> refined.Submission) students))"

text\<open>
  Replacements for it do the following in sequence:
  \<^item> Duplicate the instructions as many times as there are students,
  \<^item> Interleave those instructions with the student resource atoms, and
  \<^item> In parallel collect the submission for each student.
\<close>
definition collectionSplit_func
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> 's proc"
  where "collectionSplit_func a b l m =
      duplicateToN (length students) Instructions
    \<parallel> Identity (Parallel (map (Res \<circ> refined.Student) students))
  ;;  swapInterleave (replicate (length students) (Copyable Instructions))
                     (map (Res \<circ> refined.Student) students)
  ;;  par_process_list (map collectStudent students)"

lemma collectionSplit_func [simp]:
  shows " input (collectionSplit_func a b l m)
        = Copyable Instructions \<odot> Resource.Parallel (map (Resource.Res \<circ> Student) students)"
    and " output (collectionSplit_func a b l m)
        = Resource.Parallel (map (Resource.Res \<circ> Submission) students)"
    and "valid (collectionSplit_func a b l m)"
proof -
  show " input (collectionSplit_func a b l m)
       = Copyable Instructions \<odot> Resource.Parallel (map (Resource.Res \<circ> Student) students)"
    by (simp add: collectionSplit_func_def)
  show " output (collectionSplit_func a b l m)
       = Resource.Parallel (map (Resource.Res \<circ> Submission) students)"
    by (simp_all add: collectionSplit_func_def comp_def collectStudent_def)
       (metis append.right_neutral resource_drop)
  show "valid (collectionSplit_func a b l m)"
    unfolding collectionSplit_func_def
  proof (induct students)
    case Nil then show ?case by simp
  next
    case (Cons a as)
    then show ?case
      by (simp add: nresource_simp collectStudent_def)
         (metis (no_types, lifting) resource_empty resource_par_def resource_par_is_parallel(1))
  qed
qed

end

text\<open>
  Refinement of the monolithic collection of submissions is then substitution with the above target
  condition and replacement function.
\<close>
definition collectionSplit :: "'s proc \<Rightarrow> 's proc"
  where "collectionSplit = process_subst collectionSplit_cond collectionSplit_func"

lemma collectionSplit [simp]:
  "input (collectionSplit x) = input x"
  "output (collectionSplit x) = output x"
  "valid (collectionSplit x) = valid x"
proof -
  show "input (collectionSplit x) = input x"
    unfolding collectionSplit_def
    by (rule process_subst_input) (simp add: collectionSplit_cond_def)
  show "output (collectionSplit x) = output x"
    unfolding collectionSplit_def
    by (rule process_subst_output) (simp_all add: collectionSplit_cond_def)
  show "valid (collectionSplit x) = valid x"
    unfolding collectionSplit_def
    by (rule process_subst_valid) (simp_all add: collectionSplit_cond_def)
qed

subsection\<open>Refined Marking\<close>

text\<open>In a similar way we can split the marking action, but the replacement is simpler in this case.\<close>

text\<open>There is an action to mark an individual submission\<close>
definition markStudent :: "'s \<Rightarrow> 's proc"
  where "markStudent s =
  Primitive (Res (Submission s)) (Res (Mark s)) (STR ''Mark submission of '' + name s) ()"

text\<open>
  Target condition for the action to replace uses its input and output, since those are required for
  the replacement to preserve validity (and in this case they also uniquely identify the action).
\<close>
definition markSplit_cond
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> bool"
  where "markSplit_cond a b l m = (
  a = Parallel (map (Res \<circ> refined.Submission) students) \<and>
  b = Parallel (map (Res \<circ> refined.Mark) students))"

text\<open>Replacements for it just mark all submissions in parallel\<close>
definition markSplit_func
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> 's proc"
  where "markSplit_func a b l m = par_process_list (map markStudent students)"

lemma markSplit_func [simp]:
  "input (markSplit_func a b l m) = Resource.Parallel (map (Resource.Res \<circ> Submission) students)"
  "output (markSplit_func a b l m) = Resource.Parallel (map (Resource.Res \<circ> Mark) students)"
  "valid (markSplit_func a b l m)"
  unfolding markSplit_func_def
  by (induct students) (simp_all add: markStudent_def)

text\<open>
  Refinement of the monolithic marking action is then substitution with the above target condition
  and replacement function.
\<close>
definition markSplit :: "'s proc \<Rightarrow> 's proc"
  where "markSplit = process_subst markSplit_cond markSplit_func"

lemma markSplit [simp]:
  "input (markSplit x) = input x"
  "output (markSplit x) = output x"
  "valid (markSplit x) = valid x"
proof -
  show "input (markSplit x) = input x"
    unfolding markSplit_def
    by (rule process_subst_input) (simp add: markSplit_cond_def)
  show "output (markSplit x) = output x"
    unfolding markSplit_def
    by (rule process_subst_output) (simp_all add: markSplit_cond_def)
  show "valid (markSplit x) = valid x"
    unfolding markSplit_def
    by (rule process_subst_valid) (simp_all add: markSplit_cond_def)
qed

subsection\<open>Refined Submission of Marks\<close>

text\<open>And we can split the submission of marks, again with a simple replacement.\<close>

text\<open>There is an action to submit an individual mark\<close>
definition submitMark :: "'s \<Rightarrow> 's proc"
  where "submitMark s =
  Primitive (Res (Mark s)) (Res (MarkSubmitted s)) (STR ''Submit mark of '' + name s) ()"

text\<open>
  Target condition for the action to replace uses its input and output, since those are required for
  the replacement to preserve validity (and in this case they also uniquely identify the action).
\<close>
definition submitSplit_cond
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> bool"
  where "submitSplit_cond a b l m = (
  a = Parallel (map (Res \<circ> refined.Mark) students) \<and>
  b = Parallel (map (Res \<circ> refined.MarkSubmitted) students))"

text\<open>Replacements for it just submit all marks in parallel\<close>
definition submitSplit_func
    :: "('s lres, cres) resource \<Rightarrow> ('s lres, cres) resource \<Rightarrow> String.literal \<Rightarrow> unit \<Rightarrow> 's proc"
  where "submitSplit_func a b l m = par_process_list (map submitMark students)"

lemma submitSplit_func [simp]:
  "input (submitSplit_func a b l m) = Resource.Parallel (map (Resource.Res \<circ> Mark) students)"
  " output (submitSplit_func a b l m)
  = Resource.Parallel (map (Resource.Res \<circ> MarkSubmitted) students)"
  "valid (submitSplit_func a b l m)"
  unfolding submitSplit_func_def
  by (induct students) (simp_all add: submitMark_def)

text\<open>
  Refinement of the monolithic submission of marks is then substitution with the above target
  condition and replacement function.
\<close>
definition submitSplit :: "'s proc \<Rightarrow> 's proc"
  where "submitSplit = process_subst submitSplit_cond submitSplit_func"

lemma submitSplit [simp]:
  "input (submitSplit x) = input x"
  "output (submitSplit x) = output x"
  "valid (submitSplit x) = valid x"
proof -
  show "input (submitSplit x) = input x"
    unfolding submitSplit_def
    by (rule process_subst_input) (simp add: submitSplit_cond_def)
  show "output (submitSplit x) = output x"
    unfolding submitSplit_def
    by (rule process_subst_output) (simp_all add: submitSplit_cond_def)
  show "valid (submitSplit x) = valid x"
    unfolding submitSplit_def
    by (rule process_subst_valid) (simp_all add: submitSplit_cond_def)
qed

subsection\<open>Refined Marking Process\<close>

text\<open>Full refinement first refines the resources and then applies the three action refinements\<close>
definition markingProcess :: "'s proc"
  where "markingProcess =
  submitSplit
  ( markSplit
    ( collectionSplit
      ( process_refineRes refinement id abstract.markingProcess)))"

context begin

text\<open>
  Refined marking process is still valid and has almost the same input and output, the input
  students atom just gets refined into a parallel combination of atoms for all individual students.
\<close>
qualified lemma markingProcess:
  shows "valid markingProcess"
    and " input markingProcess
        = Copyable Instructions \<odot> Parallel (map (Resource.Res \<circ> Student) students)"
    and "output markingProcess = Res MarksReleased"
  using markingProcess_refined by (simp_all add: markingProcess_def)

end

subsection\<open>Code Generation\<close>

primrec equal_lres :: "'a refined.lres \<Rightarrow> 'a refined.lres \<Rightarrow> bool"
  where
    "equal_lres (refined.Student s) y = (case y of refined.Student s' \<Rightarrow> s = s' | _ \<Rightarrow> False)"
  | "equal_lres (refined.Submission s) y = (case y of refined.Submission s' \<Rightarrow> s = s' | _ \<Rightarrow> False)"
  | "equal_lres (refined.Mark s) y = (case y of refined.Mark s' \<Rightarrow> s = s' | _ \<Rightarrow> False)"
  | "equal_lres (refined.MarkSubmitted s) y =
      (case y of refined.MarkSubmitted s' \<Rightarrow> s = s' | _ \<Rightarrow> False)"
  | "equal_lres refined.MarksReleased y = (case y of refined.MarksReleased \<Rightarrow> True | _ \<Rightarrow> False)"

lemma equal_lres_eq:
  "equal_lres x y = (x = y)"
  by (cases x ; cases y ; simp)

primrec equal_cres :: "cres \<Rightarrow> cres \<Rightarrow> bool"
  where "equal_cres Instructions y = True"

lemma equal_cres_eq:
  "equal_cres x y = (x = y)"
  by (metis (full_types) refined.equal_cres.simps abstract.cres.exhaust)

end

instantiation refined.lres :: (equal) equal
begin
definition [simp]: "equal_lres \<equiv> refined.equal_lres"

instance
proof
  fix x y :: "'a refined.lres"
  show "equal_class.equal x y = (x = y)"
    using refined.equal_lres_eq equal_lres_def by simp
qed
end
instantiation abstract.cres :: equal
begin
definition [simp]: "equal_cres \<equiv> refined.equal_cres"

instance
proof
  fix x y :: abstract.cres
  show "equal_class.equal x y = (x = y)"
    using refined.equal_cres_eq equal_cres_def by simp
qed
end

code_datatype refined.lres.Student refined.lres.Submission refined.lres.Mark
  refined.lres.MarkSubmitted refined.lres.MarksReleased

lemmas [code] =
  refined.lres.case
  refined.equal_lres.simps
  refined.equal_cres.simps
  refined.markingProcess_def
  refined.collectionSplit_def
  refined.collectionSplit_cond_def
  refined.collectionSplit_func_def
  refined.markSplit_def
  refined.markSplit_cond_def
  refined.markSplit_func_def
  refined.submitSplit_def
  refined.submitSplit_cond_def
  refined.submitSplit_func_def
  refined.collectStudent_def
  refined.duplicateToN.simps
  refined.markStudent_def
  refined.swapInterleave.simps
  refined.submitMark_def
  refined.refinement.simps

end