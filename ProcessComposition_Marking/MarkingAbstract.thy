theory MarkingAbstract
  imports
    ProcessComposition.Process
begin

text\<open>
  This example aims to demonstrate the use of resource refinement and basic action substitution.

  We represent the process of marking a number of student course work submissions from two points of
  view: before and after the actual submissions are known (abstract and refined respectively).
  Before we get the actual submissions the process composition is the general plan for marking.
  After we get the actual submissions we can refine that plan with actions for marking each
  submission, allowing for the possibility of better planning or monitoring.
\<close>

section\<open>Abstract Model of Marking\<close>

locale abstract
begin

text\<open>Liner resource atoms represent the students, submissions, marks and their status\<close>
datatype lres = Students \<comment> \<open>Abstract idea of all students\<close>
  | Submissions \<comment> \<open>Abstract idea of all students' submissions\<close>
  | Marks \<comment> \<open>Abstract idea of all students' marks\<close>
  | MarksSubmitted \<comment> \<open>All marks have been submitted\<close>
  | MarksReleased \<comment> \<open>All marks have been released\<close>

text\<open>Copyable resource atoms represent the instructions distributed to each student\<close>
datatype cres = Instructions

text\<open>There is an action to collect the submissions of all students\<close>
definition "collectSubs =
  Primitive (Copyable Instructions \<odot> Res Students) (Res Submissions) STR ''Collect Submissions'' ()"

text\<open>There is an action to mark all the submissions\<close>
definition "markAll =
  Primitive (Res Submissions) (Res Marks) STR ''Mark Submissions'' ()"

text\<open>There is an action to submit all of the marks\<close>
definition "submitMarks =
  Primitive (Res Marks) (Res MarksSubmitted) STR ''Submit Marks'' ()"

text\<open>There is an action to release all of the marks\<close>
definition "releaseMarks =
  Primitive (Res MarksSubmitted) (Res MarksReleased) STR ''Release Marks'' ()"

context
  includes process_notation
begin

text\<open>
  Marking the course work assignment means collecting the submissions, marking all of them,
  submitting all of the marks and then releasing them
\<close>
definition "markingProcess = collectSubs ;; markAll ;; submitMarks ;; releaseMarks"

text\<open>Marking process is valid, requires instructions and students and results in submitted marks\<close>
qualified lemma markingProcess:
  shows "valid markingProcess"
    and "input markingProcess = Copyable Instructions \<odot> Res Students"
    and "output markingProcess = Res MarksReleased"
  by (simp_all add: markingProcess_def releaseMarks_def submitMarks_def markAll_def collectSubs_def)

end

end

subsection\<open>Code Generation\<close>

text\<open>We need extra steps to set up code generation from the locale\<close>

code_datatype abstract.lres.Students abstract.lres.Submissions
  abstract.lres.Marks abstract.lres.MarksSubmitted abstract.lres.MarksReleased

code_datatype abstract.cres.Instructions

lemmas [code] =
  abstract.markingProcess_def
  abstract.collectSubs_def
  abstract.markAll_def
  abstract.submitMarks_def
  abstract.releaseMarks_def

end