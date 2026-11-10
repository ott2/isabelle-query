"""Minimal (Pure) method / attribute / keyword namespace — GENERATED, do not edit.

The committed *fallback* table; the runtime resolves the session-exact table.

Regenerate with::

    python3 scripts/extract_isabelle_namespace.py

This is the *minimal* fallback table (the Pure core).  At runtime the router
resolves the session-exact table from a loaded heap; this ships for when
Isabelle is unavailable — so it deliberately omits HOL's auto/blast/induct,
which come from session resolution, not from assuming HOL.

Provenance:
    Isabelle:    Isabelle2025-2
    Extracted:   2026-11-10
    Methods:     37 (Pure image method name space — ML_process -l Pure)
    Attributes:  101 (Pure image attribute name space)
    Keywords:    224 (Pure.thy keyword table + thy_header bootstrap; /Applications/Isabelle2025-2.app/src)

These power isabelle_query's token *router*: a proof-body token is a fact
citation (a call-graph edge) only if it is none of a proof method, an
attribute, a keyword, or a numeral.  Method occurrences are not discarded —
they feed the `methods` query.
"""

# proof methods (`by simp`, `apply (rule r)`) — never a fact citation, but a
# method-usage datum.
PROOF_METHODS = frozenset({
    '-', 'assumption', 'atomize', 'cut_tac', 'drule', 'drule_tac', 'elim',
    'erule', 'erule_tac', 'fact', 'fail', 'fold', 'frule', 'frule_tac',
    'goal_cases', 'insert', 'intro', 'intro_classes', 'intro_locales',
    'raw_tactic', 'rename_tac', 'rotate_tac', 'rule', 'rule_tac', 'simp',
    'simp_all', 'sleep', 'standard', 'subgoal_tac', 'subproofs', 'succeed',
    'tactic', 'thin_tac', 'this', 'unfold', 'unfold_locales', 'use',
})

# attributes (`[OF g]`, `simp del:`, `[simp]`) — modifiers, never citations.
ATTRIBUTES = frozenset({
    'ML_catch_all', 'ML_debugger', 'ML_environment', 'ML_exception_debugger',
    'ML_exception_trace', 'ML_print_depth', 'ML_read_global',
    'ML_source_trace', 'ML_write_global', 'OF', 'THEN', 'abs_def', 'atomize',
    'attribute', 'case_conclusion', 'case_names', 'cases_open', 'cite_macro',
    'code', 'code_only_single_equation', 'code_prepend_allowed',
    'code_strict_drop', 'cong', 'cong_format', 'constraints', 'consumes',
    'defn', 'dest', 'elim', 'elim_format', 'eta_contract',
    'extraction_expand', 'extraction_expand_def', 'folded', 'goals_limit',
    'intro', 'kind', 'names_long', 'names_short', 'names_unique', 'no_vars',
    'of', 'params', 'quick_and_dirty', 'rename_abs', 'rotated', 'rule',
    'rule_format', 'rule_trace', 'rulify', 'show_abbrevs', 'show_consts',
    'show_consts_markup', 'show_hyps', 'show_main_goal', 'show_markup',
    'show_question_marks', 'show_results', 'show_reverted_improvements',
    'show_sorts', 'show_structs', 'show_tags', 'show_types', 'show_variants',
    'simp', 'simp_break', 'simp_debug', 'simp_depth_limit', 'simp_trace',
    'simp_trace_depth_limit', 'simp_trace_new', 'simplified', 'simproc',
    'sym', 'symmetric', 'syntax_ambiguity_limit', 'syntax_ambiguity_warning',
    'syntax_ast_stats', 'syntax_ast_trace', 'tagged', 'thy_output_break',
    'thy_output_cartouche', 'thy_output_display', 'thy_output_indent',
    'thy_output_margin', 'thy_output_modes', 'thy_output_quotes',
    'thy_output_source', 'thy_output_source_cartouche', 'trace_locales',
    'trans', 'unfold_abs_def', 'unfolded', 'unify_search_bound',
    'unify_trace', 'unify_trace_bound', 'unify_trace_failure',
    'unify_trace_simp', 'unify_trace_types', 'untagged', 'where',
})

# outer-syntax keywords (commands, proof language, quasi-commands, bootstrap):
# structural, never a fact citation.
KEYWORDS = frozenset({
    'ML', 'ML_command', 'ML_export', 'ML_file', 'ML_file_debug',
    'ML_file_no_debug', 'ML_prf', 'ML_val', 'ROOTS_file', 'SML_export',
    'SML_file', 'SML_file_debug', 'SML_file_no_debug', 'SML_import',
    'abbreviation', 'abbrevs', 'adhoc_overloading', 'alias', 'also', 'and',
    'apply', 'apply_end', 'assume', 'assumes', 'attribute_setup',
    'axiomatization', 'back', 'begin', 'bibtex_file', 'binder', 'bundle',
    'by', 'case', 'chapter', 'class', 'class_deps', 'code_datatype',
    'compile_generated_files', 'congproc', 'consider', 'constrains',
    'consts', 'context', 'corollary', 'declaration', 'declare',
    'default_sort', 'defer', 'define', 'defines', 'definition', 'done',
    'end', 'experiment', 'export_classpath', 'export_generated_files',
    'external_file', 'extract', 'extract_type', 'finally', 'find_consts',
    'find_theorems', 'fix', 'fixes', 'for', 'from', 'full_prf',
    'generate_file', 'global_interpretation', 'have', 'help', 'hence',
    'hide_class', 'hide_const', 'hide_fact', 'hide_type', 'identifier', 'if',
    'imports', 'in', 'include', 'includes', 'including', 'infix', 'infixl',
    'infixr', 'instance', 'instantiation', 'interpret', 'interpretation',
    'is', 'judgment', 'keywords', 'lemma', 'lemmas', 'let', 'local_setup',
    'locale', 'locale_deps', 'method_setup', 'moreover', 'named_theorems',
    'next', 'no_adhoc_overloading', 'no_notation', 'no_syntax',
    'no_translations', 'no_type_notation', 'nonterminal', 'notation', 'note',
    'notepad', 'notes', 'obtain', 'obtains', 'oops', 'open', 'open_bundle',
    'opening', 'oracle', 'output', 'overloaded', 'overloading', 'paragraph',
    'parse_ast_translation', 'parse_translation', 'passive', 'pervasive',
    'prefer', 'premises', 'presume', 'prf', 'print_ML_antiquotations',
    'print_abbrevs', 'print_antiquotations', 'print_ast_translation',
    'print_attributes', 'print_bundles', 'print_cases', 'print_classes',
    'print_codesetup', 'print_commands', 'print_context',
    'print_context_tracing', 'print_definitions', 'print_defn_rules',
    'print_facts', 'print_interps', 'print_locale', 'print_locales',
    'print_methods', 'print_options', 'print_rules', 'print_simpset',
    'print_state', 'print_statement', 'print_syntax', 'print_term_bindings',
    'print_theorems', 'print_theory', 'print_trans_rules',
    'print_translation', 'private', 'proof', 'prop', 'proposition', 'qed',
    'qualified', 'realizability', 'realizers', 'rewrites',
    'scala_build_generated_files', 'schematic_goal', 'section', 'setup',
    'show', 'shows', 'simproc_setup', 'sorry', 'structure', 'subclass',
    'subgoal', 'sublocale', 'subparagraph', 'subsection', 'subsubsection',
    'supply', 'syntax', 'syntax_consts', 'syntax_declaration',
    'syntax_types', 'term', 'text', 'text_raw', 'then', 'then have',
    'then show', 'theorem', 'theory', 'thm', 'thm_deps', 'thm_oracles',
    'thus', 'thy_deps', 'translations', 'txt', 'typ', 'type_alias',
    'type_notation', 'type_synonym', 'typed_print_translation', 'typedecl',
    'ultimately', 'unbundle', 'unchecked', 'unfolding', 'unused_thms',
    'using', 'weak_congproc', 'welcome', 'when', 'where', 'with', 'write',
})
