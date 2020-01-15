hook global BufCreate .*\.v %{
    set-option buffer filetype coq
}

hook global WinSetOption filetype=coq %{
    require-module coq

    set-option window static_words %opt{coq_static_words}

    #hook window ModeChange pop:insert:.* -group coq-trim-indent %{ try %{ execute-keys -draft <a-x>s^\h+$<ret>d } }
    hook window InsertChar \n -group coq-indent coq-indent-on-new-line

    hook -once -always window WinSetOption filetype=.* %{ remove-hooks window coq-.+ }
}

hook -group coq-highlight global WinSetOption filetype=coq %{
    add-highlighter window/coq ref coq
    hook -once -always window WinSetOption filetype=.* %{ remove-highlighter window/coq }
}

provide-module coq %§

add-highlighter shared/coq regions
add-highlighter shared/coq/code default-region group
add-highlighter shared/coq/comment region \(\* \*\) fill comment

evaluate-commands %sh{
    keywords_gallina='_ as at cofix else end exists exists2 fix for
                      forall fun if IF in let match mod return
                      SProp Prop Set Type then using where with'
    keywords_tactics='abstract all assert_fails assert_succeeds
                      constr context do else end eval exactly_once
                      fail first fresh fun gfail goal guard idtac
                      in lazymatch let Ltac match multimatch numgoals
                      of once only par progress rec repeat reverse
                      solve then time timeout try tryif type type_term
                      uconstr with'
    commands='Abort About Add Add\\ Field Add\\ LoadPath Add\\ ML\\ Path Add\\ Morphism Add\\ Parametric\\ Morphism Add\\ Parametric\\ Relation Add\\ Rec\\ LoadPath Add\\ Rec\\ ML\\ Path Add\\ Relation Add\\ Ring Add\\ Setoid Admit\\ Obligations Admitted Arguments Axiom Axioms
              Back BackTo Backtrack Bind\\ Scope
              Canonical Cd Check Class Close\\ Scope Coercsion CoFixpoint CoInductive Collection Combined\\ Scheme Compute Conjecture Conjectures Constraint Context Corollary Create\\ HintDb Cumulative
              Declare\\ Custom\\ Entry Declare\\ Instance Declare\\ Left\\ Step Declare\\ ML\\ Module Declare\\ Reduction Declare\\ Right\\ Step Declare\\ Scope Defined Definition Delimit\\ Scope Derive Derive\\ Inversion Drop
              End Eval Example Existential Existing\\ Instance Export Extract\\ Constant Extract\\ Inductive Extract\\ Inlined\\ Constant Extraction Extraction\\ Blacklist Extraction\\ Implicit Extraction\\ Inline Extraction\\ Language Extraction\\ Library Extraction\\ NoInline Extraction\\ TestCompile
              Fact Fail Fixpoint Focus From\\ Require Function Functional\\ Scheme
              Generalizable Generalizable\\ All\\ Variables Generalizable\\ No\\ Variables Global Global\\ Close\\ Scope Global\\ Generalizable Global\\ Instance Global\\ Opaque Global\\ Open\\ Scope Global\\ Transparent Goal Grab\\ Existential\\ Variables Guarded
              Hint Hint\\ Constants Hint\\ Constructors Hint\\ Cut Hint\\ Extern Hint\\ Immediate Hint\\ Mode Hint\\ Opaque Hint\\ Resolve Hint\\ Rewrite Hint\\ Transparent Hint\\ Unfold Hint\\ Variables Hint\\ View\\ for Hint\\ View\\ for\\ apply Hint\\ View\\ for\\ move Hypotheses Hypothesis
              Identity\\ Coercsion Implicit\\ Types Import Include Inductive Infix Info Inline Inspect Instance
              Lemma Let Let\\ CoFixpoint Let\\ Fixpoint Load Local Local\\ Close\\ Scope Local\\ Declare\\ Custom\\ Entry Local\\ Definition Local\\ Notation Local\\ Open\\ Scope Local\\ Parameter Locate Locate\\ File Locate\\ Library Ltac
              Module Module\\ Type Monomorhpic
              Next\\ Obligation NonCumulative Notation Numeral\\ Notation
              Obligation Obligation\\ Tactic Obligations Opaque Open\\ Scope Optimize\\ Heap Optimize\\ Proof
              Parameter Parameters Polymorphic Polymorphic\\ Constraint Polymorphic\\ Universe Prenex\\ Implicits Preterm Primitive Print Print\\ All Print\\ All\\ Dependencies Print\\ Assumtions Print\\ Canonical\\ Projections Print\\ Classes Print\\ Coercion\\ Paths Print\\ Coercions Print\\ Custom\\ Grammar Print\\ Extraction\\ Blacklist Print\\ Extraction\\ Inline Print\\ Firstorder\\ Solver Print\\ Grammar\\ constr Print\\ Grammar\\ pattern Print\\ Grammar\\ tactic Print\\ Graph Print\\ Hint Print\\ HintDb Print\\ Implicit Print\\ Instances Print\\ Libraries Print\\ LoadPath Print\\ Ltac Print\\ Ltac\\ Signatures Print\\ ML\\ Modules Print\\ ML\\ Path Print\\ Module Print\\ Module\\ Type Print\\ Opaque\\ Dependencies Print\\ Options Print\\ Rewrite\\ HintDb Print\\ Scope Print\\ Scopes Print\\ Strategy Print\\ Table\\ @table Print\\ Tables Print\\ Term Print\\ Transparent\\ Dependencies Print\\ Universes Print\\ Universes\\ Subgraph Print\\ Visibility Program\\ Definition Program\\ Fixpoint Program\\ Instance Program\\ Lemma Proof Proposition Pwd
              Qed Quit
              Save Scheme Scheme\\ Equality Search SearchAbout SearchHead SearchPattern SearchRewrite Section Separate\\ Extraction Set Show Show\\ Conjectures Show\\ Existentials Show\\ Intro Show\\ Intros Show\\ Ltac\\ Profile Show\\ Obligation\\ Tactic Show\\ Proof Show\\ Script Show\\ Universes Solve\\ All\\ Obligations Solve\\ Obligations Strategy String\\ Notation Structure SubClass
              Tactic\\ Notation Test Theorem Time Timeout Transparent Typeclasses\\ eauto Typeclasses\\ Opaque Typeclasses\\ Transparent Undelimit\\ Scope
              Undo Unfocus Unfocused Universe Unset Unshelve
              Variable Variables Variant'
    tactics='abstract absurd admit all apply apply\\ in apply\\ in\\ as assert assert_fails assert_succeeds assumption auto autoapply autorewrite autounfold
             btauto by
             case cbn cbv change change_no_check classical_left classical_right clear clearbody cofix compare compute congr congruence congruence\\ with constr_eq constr_eq_strict constructor contradict contradiction convert_concl_no_check cut cutrewrite cycle
             dependent debug\\ auto debug\\ trivial decide\\ equality decompose  destruct destruct\\ eqn dintuition discriminate discrR do done double\\ induction dtauto
             eapply eassert eassumption easy eauto ecase econstructor edestruct ediscriminate eelim eenough eexact eexists einduction einjection eintros eleft elim elim\\ with elimtype enough epose epose\\ proof eremember erewrite eright eset esimplify_eq esplit evar exact exact_no_check exactly_once exfalso exists
             f_equal fail field field_simplify field_simplify_eq finish_timing first first\\ last firstorder fix fold function\\ induction functional\\ inversion
             generalize generally have gfail give_up guard
             has_evar have hnf
             idtac in induction induction\\ using info_trivial injection instantiate intro intros intuition inversion inversion\\ using inversion_clear inversion_sigma is_evar is_var
             lapply last last\\ first lazy left let\\ lia lra ltac-seq
             match\\ goal move move\\ after move\\ at\\ bottom move\\ at\\ top move\\ before
             native_cast_no_check native_compute nia notypeclasses\\ refine now nra nsatz
             omega once only optimize_heap over
             par pattern pose pose\\ proof progress psatz
             red refine reflexivity remember rename repeat replace reset\\ ltac\\ profile restart_timer revert revert\\ dependent revgoals rewrite rewrite_strat right ring ring_simplify rtauto
             set setoid_reflexivity setoid_replace setoid_rewrite setoid_symmetry setoid_transitivity shelve shelve_unifiable show\\ ltac\\ profile simpl simple\\ apply simple\\ destruct simple\\ eapply simple\\ induction simple\\ inversion simple\\ notypeclasses\\ refine simple\\ refine simplify_eq solve solve_constraints specialize split split_Rabs split_Rmult start\\ ltac\\ profiling stepl stepr stop\\ ltac\\ profiling subst suff suffices swap symmetry
             tauto time time_constr timeout transitivity transparent_abstract trivial try tryif typeclasses\\ eauto
             under unfold unify unlock unshelve
             vm_cast_no_check vm_compute
             without\\ loss wlog'

    join() { sep=$2; eval set -- $1; IFS="$sep"; echo "$*"; }

    printf %s\\n "declare-option str-list coq_static_words $(join "${keywords_gallina} ${keywords_tactics} ${commands} ${tactics}" ' ')"
    printf %s "
        add-highlighter shared/coq/code/ regex \b($(join "${keywords_gallina}" '|'))\b 0:keyword
        add-highlighter shared/coq/code/ regex \b($(join "${keywords_tactics}" '|'))\b 0:keyword
        add-highlighter shared/coq/code/ regex \b($(join "${commands}" '|'))\b 0:builtin
        add-highlighter shared/coq/code/ regex \b($(join "${tactics}" '|'))\b 0:value
        add-highlighter shared/coq/code/ regex (admit|Admit|Admitted|Abort|give_up) 0:error
    "
}

define-command -hidden coq-indent-on-new-line %~
    evaluate-commands -draft -itersel %@
        try %{ execute-keys -draft <semicolon>K<a-&> }
        try %{ execute-keys -draft k<a-x> s \h+$ <ret>d }
        try %[ execute-keys -draft <semicolon><a-F>)MB <a-k> \A(if|then|else)\h*\(.*\)\h*\n\h*\n?\z <ret> s \A|.\z <ret> 1<a-&>1<a-space><a-gt> ]
        try %[ execute-keys -draft <semicolon><a-F>)MB <a-k> \A(:=)\h*\(.*\)\h*\n\h*\n?\z <ret> s \A|.\z <ret> 1<a-&>1<a-space><a-gt> ]
    @
~

§
