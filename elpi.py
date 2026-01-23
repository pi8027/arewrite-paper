"""
    pygments.lexers.elpi
    ~~~~~~~~~~~~~~~~~~~~

    Lexer for the `Elpi <http://github.com/LPCIC/elpi>`_ programming language.

    :copyright: Copyright 2006-2024 by the Pygments team, see AUTHORS.
    :license: BSD, see LICENSE for details.
"""

from pygments.lexer import RegexLexer, bygroups, default, words, include, using
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation

__all__ = ['ElpiLexer', 'RocqLexer']

class RocqLexer(RegexLexer):
    """
    For the Rocq Prover.
    """

    name = 'Rocq Prover'
    url = 'https://rocq-prover.org/'
    aliases = ['coq', 'rocq', 'rocq-prover']
    filenames = ['*.v']
    mimetypes = ['text/x-coq', 'text/x-rocq']
    version_added = '1.5'

    flags = 0 # no re.MULTILINE

    keywords1 = (
        # Vernacular commands
        'Section', 'Module', 'End', 'Require', 'Import', 'Export', 'Include', 'Variable',
        'Variables', 'Parameter', 'Parameters', 'Axiom', 'Axioms', 'Hypothesis',
        'Hypotheses', 'Notation', 'Local', 'Tactic', 'Reserved', 'Scope',
        'Open', 'Close', 'Bind', 'Declare', 'Delimit', 'Definition', 'Example', 'Let',
        'Ltac', 'Ltac2', 'Fixpoint', 'CoFixpoint', 'Morphism', 'Relation', 'Implicit',
        'Arguments', 'Types', 'Contextual', 'Strict', 'Prenex',
        'Implicits', 'Inductive', 'CoInductive', 'Record', 'Structure',
        'Variant', 'Canonical', 'Coercion', 'Theorem', 'Lemma', 'Fact',
        'Remark', 'Corollary', 'Proposition', 'Property', 'Goal',
        'Proof', 'Restart', 'Save', 'Qed', 'Defined', 'Abort', 'Admitted',
        'Hint', 'Resolve', 'Rewrite', 'View', 'Search', 'Compute', 'Eval',
        'Show', 'Print', 'Printing', 'All', 'Graph', 'Projections', 'inside',
        'outside', 'Check', 'Global', 'Instance', 'Class', 'Existing',
        'Universe', 'Polymorphic', 'Monomorphic', 'Context', 'Scheme', 'From',
        'Undo', 'Fail', 'Function', 'Program', 'Elpi', 'Extract', 'Opaque',
        'Transparent', 'Unshelve', 'Next Obligation',
    )
    keywords2 = (
        # Gallina
        'forall', 'exists', 'exists2', 'fun', 'fix', 'cofix', 'struct',
        'match', 'end',  'in', 'return', 'let', 'if', 'is', 'then', 'else',
        'for', 'of', 'nosimpl', 'with', 'as',
    )
    keywords3 = (
        # Sorts
        'Type', 'Prop', 'SProp', 'Set',
    )
    keywords4 = (
        # Tactics
        'pose', 'set', 'move', 'case', 'elim', 'apply', 'clear', 'hnf', 'intro',
        'intros', 'generalize', 'rename', 'pattern', 'after', 'destruct',
        'induction', 'using', 'refine', 'inversion', 'injection', 'rewrite',
        'congr', 'unlock', 'compute', 'ring', 'field', 'replace', 'fold',
        'unfold', 'change', 'cutrewrite', 'simpl', 'have', 'suff', 'wlog',
        'suffices', 'without', 'loss', 'nat_norm', 'assert', 'cut', 'trivial',
        'revert', 'bool_congr', 'nat_congr', 'symmetry', 'transitivity', 'auto',
        'split', 'left', 'right', 'autorewrite', 'tauto', 'setoid_rewrite',
        'intuition', 'eauto', 'eapply', 'econstructor', 'etransitivity',
        'constructor', 'erewrite', 'red', 'cbv', 'lazy', 'vm_compute',
        'native_compute', 'subst',
        # Paper-specific ones
        'arewrite', 'airewrite',
    )
    keywords5 = (
        # Terminators
        'by', 'now', 'done', 'exact', 'reflexivity',
        'tauto', 'romega', 'omega', 'lia', 'nia', 'lra', 'nra', 'psatz',
        'assumption', 'solve', 'contradiction', 'discriminate',
        'congruence', 'admit',
        # Paper-specific ones
        'areflexivity', 'aireflexivity',
    )
    keywords6 = (
        # Control
        'do', 'last', 'first', 'try', 'idtac', 'repeat',
    )
    # 'as', 'assert', 'begin', 'class', 'constraint', 'do', 'done',
    # 'downto', 'else', 'end', 'exception', 'external', 'false',
    # 'for', 'fun', 'function', 'functor', 'if', 'in', 'include',
    # 'inherit', 'initializer', 'lazy', 'let', 'match', 'method',
    # 'module', 'mutable', 'new', 'object', 'of', 'open', 'private',
    # 'raise', 'rec', 'sig', 'struct', 'then', 'to', 'true', 'try',
    # 'type', 'val', 'virtual', 'when', 'while', 'with'
    keyopts = (
        '!=', '#', '&', '&&', r'\(', r'\)', r'\*', r'\+', ',', '-', r'-\.',
        '->', r'\.', r'\.\.', ':', '::', ':=', ':>', ';', ';;', '<', '<-',
        '<->', '=', '>', '>]', r'>\}', r'\?', r'\?\?', r'\[', r'\[<', r'\[>',
        r'\[\|', ']', '_', '`', r'\{', r'\{<', r'lp:\{\{', r'\|', r'\|]', r'\}', '~', '=>',
        r'/\\', r'\\/', r'\{\|', r'\|\}',
        # 'Π', 'Σ', # Not defined in the standard library
        'λ', '¬', '∧', '∨', '∀', '∃', '→', '↔', '≠', '≤', '≥',
    )
    operators = r'[!$%&*+\./:<=>?@^|~-]'
    prefix_syms = r'[!?~]'
    infix_syms = r'[=<>@^|&+\*/$%-]'

    tokens = {
        'root': [
            (r'\s+', Text),
            (r'false|true|\(\)|\[\]', Name.Builtin.Pseudo),
            (r'\(\*', Comment, 'comment'),
            (r'\b(?:[^\W\d][\w\']*\.)+[^\W\d][\w\']*\b', Name),
            (r'\bEquations\b\??', Keyword.Namespace),
            (r'\b(Elpi)(\s+)(Program|Query|Accumulate|Command|Typecheck|Db|Export|Tactic)?\b', bygroups(Keyword.Namespace,Text,Keyword.Namespace)),
            # Very weak heuristic to distinguish the Set vernacular from the Set sort
            (r'\bUnset\b|\bSet(?=[ \t]+[A-Z][a-z][^\n]*?\.)', Keyword.Namespace, 'set-options'),
            (r'\b(?:String|Number)\s+Notation', Keyword.Namespace, 'sn-notation'),
            (words(keywords1, prefix=r'\b', suffix=r'\b'), Keyword.Namespace),
            (words(keywords2, prefix=r'\b', suffix=r'\b'), Keyword),
            (words(keywords3, prefix=r'\b', suffix=r'\b'), Keyword.Type),
            (words(keywords4, prefix=r'\b', suffix=r'\b'), Keyword),
            (words(keywords5, prefix=r'\b', suffix=r'\b'), Keyword.Pseudo),
            (words(keywords6, prefix=r'\b', suffix=r'\b'), Keyword.Reserved),
            # (r'\b([A-Z][\w\']*)(\.)', Name.Namespace, 'dotted'),
            (r'\b([A-Z][\w\']*)', Name),
            (r'({})'.format('|'.join(keyopts[::-1])), Operator),
            (rf'({infix_syms}|{prefix_syms})?{operators}', Operator),

            (r"[^\W\d][\w']*", Name),

            (r'\d[\d_]*', Number.Integer),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),

            (r"'(?:(\\[\\\"'ntbr ])|(\\[0-9]{3})|(\\x[0-9a-fA-F]{2}))'", String.Char),

            (r"'.'", String.Char),
            (r"'", Keyword),  # a stray quote is another syntax element

            (r'"', String.Double, 'string'),

            (r'[~?][a-z][\w\']*:', Name),
            (r'\S', Name.Builtin.Pseudo),
        ],
        'set-options': [
            (r'\s+', Text),
            (r'[A-Z]\w*', Keyword.Namespace),
            (r'"', String.Double, 'string'),
            (r'\d+', Number.Integer),
            (r'\.', Punctuation, '#pop'),
        ],
        'sn-notation': [
            (r'\s+', Text),
            # Extra keywords to highlight only in this scope
            (r'\b(?:via|mapping|abstract|warning|after)\b', Keyword),
            (r'=>|[()\[\]:,]', Operator),
            (r'\b[^\W\d][\w\']*(?:\.[^\W\d][\w\']*)*\b', Name),
            (r'\d[\d_]*', Number.Integer),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'\(\*', Comment, 'comment'),
            (r'\.', Punctuation, '#pop'),
        ],
        'comment': [
            # Consume comments like ***** as one token
            (r'([^(*)]+|\*+(?!\)))+', Comment),
            (r'\(\*', Comment, '#push'),
            (r'\*\)', Comment, '#pop'),
            (r'[(*)]', Comment),
        ],
        'string': [
            (r'[^"]+', String.Double),
            (r'""', String.Double),
            (r'"', String.Double, '#pop'),
        ],
        'dotted': [
            (r'\s+', Text),
            (r'\.', Punctuation),
            (r'[A-Z][\w\']*(?=\s*\.)', Name.Namespace),
            (r'[A-Z][\w\']*', Name.Class, '#pop'),
            (r'[a-z][a-z0-9_\']*', Name, '#pop'),
            default('#pop')
        ],
    }

    def analyse_text(text):
        if 'Qed' in text and 'Proof' in text:
            return 1

class ElpiLexer(RegexLexer):
    """
    Lexer for the Elpi programming language.
    """

    name = 'Elpi'
    url = 'http://github.com/LPCIC/elpi'
    aliases = ['elpi']
    filenames = ['*.elpi']
    mimetypes = ['text/x-elpi']
    version_added = '2.11'

    lcase_re = r"[a-z]"
    ucase_re = r"[A-Z]"
    digit_re = r"[0-9]"
    schar2_re = r"([+*^?/<>`'@#~=&!])"
    schar_re = rf"({schar2_re}|-|\$|_)"
    idchar_re = rf"({lcase_re}|{ucase_re}|{digit_re}|{schar_re})"
    idcharstarns_re = rf"({idchar_re}*(\.({lcase_re}|{ucase_re}){idchar_re}*)*)"
    symbchar_re = rf"({lcase_re}|{ucase_re}|{digit_re}|{schar_re}|:)"
    constant_re = rf"({ucase_re}{idchar_re}*|{lcase_re}{idcharstarns_re}|{schar2_re}{symbchar_re}*|_{idchar_re}+)"
    symbol_re = r"(,|<=>|-->|:-|:>|;|\?-|->|&|=>|\bas\b|\buvar\b|<|=<|=|==|>=|>|\bi<|\bi=<|\bi>=|\bi>|\bis\b|\br<|\br=<|\br>=|\br>|\bs<|\bs=<|\bs>=|\bs>|@|::|\[\]|`->|`:|`:=|\^|-|\+|\bi-|\bi\+|r-|r\+|/|\*|\bdiv\b|\bi\*|\bmod\b|\br\*|~|\bi~|\br~)"
    const_sym_re = rf"({constant_re}|{symbol_re}|\({symbol_re}\))"

    tokens = {
        'root': [
            include('elpi')
        ],

        'elpi': [
            include('_elpi-comment'),

            (r"(:before|:after|:if|:name)(\s*)(\")",
             bygroups(Keyword.Mode, Text.Whitespace, String.Double),
             'elpi-string'),
            (r"(:index)(\s*)(\()", bygroups(Keyword.Mode, Text.Whitespace, Punctuation),
             'elpi-indexing-expr'),
            (rf"\b(external pred|pred)(\s+)({const_sym_re})",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-pred-item'),
            (rf"\b(func)(\s+)({const_sym_re})",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-func-item'),
            (rf"\b(external type|type)(\s+)(({const_sym_re}(,\s*)?)+)",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-type'),
            (rf"\b(kind)(\s+)(({const_sym_re}|,)+)",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-type'),
            (rf"\b(typeabbrev)(\s+)({const_sym_re})",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-type'),
            (r"\b(typeabbrev)(\s+)(\([^)]+\))",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-type'),
            (r"\b(accumulate)(\s+)(\")",
             bygroups(Keyword.Declaration, Text.Whitespace, String.Double),
             'elpi-string'),
            (rf"\b(accumulate|namespace|local)(\s+)({constant_re})",
             bygroups(Keyword.Declaration, Text.Whitespace, Text)),
            (rf"\b(shorten)(\s+)({constant_re}\.)",
             bygroups(Keyword.Declaration, Text.Whitespace, Text)),
            (r"\b(pi|sigma)(\s+)([a-zA-Z][A-Za-z0-9_ ]*)(\\)",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Variable, Text)),
            (rf"\b(constraint)(\s+)(({const_sym_re}(\s+)?)+)",
             bygroups(Keyword.Declaration, Text.Whitespace, Name.Function),
             'elpi-chr-rule-start'),

            (rf"(?=[A-Z_]){constant_re}", Name.Variable),
            (rf"(?=[a-z_])({constant_re}|_)\\", Name.Variable),
            (r"_", Name.Variable),
            (rf"({symbol_re}|!|=>|;)", Keyword.Declaration),
            (constant_re, Text),
            (r"\[|\]|\||=>", Keyword.Declaration),
            (r'"', String.Double, 'elpi-string'),
            (r'`', String.Double, 'elpi-btick'),
            (r'\'', String.Double, 'elpi-tick'),
            (r'\{\{', Punctuation, 'elpi-quote'),
            (r'\{[^\{]', Text, 'elpi-spill'),
            (r"\(", Punctuation, 'elpi-in-parens'),
            (r'\d[\d_]*', Number.Integer),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),
            (r"[\+\*\-/\^\.]", Operator),
        ],
        '_elpi-comment': [
            (r'%[^\n]*\n', Comment),
            (r'/(?:\\\n)?[*](?:[^*]|[*](?!(?:\\\n)?/))*[*](?:\\\n)?/', Comment),
            (r"\s+", Text.Whitespace),
        ],
        'elpi-indexing-expr':[
            (r'[0-9 _]+', Number.Integer),
            (r'\)', Punctuation, '#pop'),
        ],
        'elpi-type': [
            (r"(ctype\s+)(\")", bygroups(Keyword.Type, String.Double), 'elpi-string'),
            (r'->', Keyword.Type),
            (r'prop', Keyword.Mode),
            (constant_re, Keyword.Type),
            (r"\(|\)", Keyword.Type),
            (r"\.", Text, '#pop'),
            include('_elpi-comment'),
        ],
        'elpi-chr-rule-start': [
            (r"\{", Punctuation, 'elpi-chr-rule'),
            include('_elpi-comment'),
        ],
        'elpi-chr-rule': [
           (r"\brule\b", Keyword.Declaration),
           (r"\\", Keyword.Declaration),
           (r"\}", Punctuation, '#pop:2'),
           include('elpi'),
        ],
        'elpi-pred-item': [
            (r"[io]:", Keyword.Mode),
            (r"\.", Text, '#pop'),
            (r",", Keyword.Mode),
            include('_elpi-inner-pred-fun'),
            (r"\)", Keyword.Mode, '#pop'),
            (r"\(", Keyword.Type, '_elpi-type-item'),
            include('_elpi-comment'),
            include('_elpi-type-item'),
        ],
        'elpi-func-item': [
            (constant_re, Keyword.Type),
            (r"\.", Text, '#pop'),
            (r",", Keyword.Mode),
            (r'->', Keyword.Mode),
            include('_elpi-inner-pred-fun'),
            (r"\)", Keyword.Mode, '#pop'),
            (r"\(", Keyword.Type, '_elpi-type-item'),
            include('_elpi-comment'),
            include('_elpi-type-item'),
        ],
        '_elpi-inner-pred-fun': [
            (r"(\()(\s*)(pred)", bygroups(Keyword.Mode,Text.Whitespace,Keyword.Declaration), 'elpi-pred-item'),
            (r"(\()(\s*)(func)", bygroups(Keyword.Mode,Text.Whitespace,Keyword.Declaration), 'elpi-func-item'),
        ],
        '_elpi-type-item': [
            (r'->', Keyword.Type),
            (constant_re, Keyword.Type),
            include('_elpi-inner-pred-fun'),
            (r"\(", Keyword.Type, '#push'),
            (r"\)", Keyword.Type, '#pop'),
            include('_elpi-comment'),
        ],

        ''

        'elpi-btick': [
            (r'[^` ]+', String.Double),
            (r'`', String.Double, '#pop'),
        ],
        'elpi-tick': [
            (r'[^\' ]+', String.Double),
            (r'\'', String.Double, '#pop'),
        ],
        'elpi-string': [
            (r'[^\"]+', String.Double),
            (r'"', String.Double, '#pop'),
        ],
        'elpi-quote': [
            (r'\}\}', Punctuation, '#pop'),
            (r"\s+", Text.Whitespace),
            (r"(lp:)(\{\{)", bygroups(Number, Punctuation), 'elpi-quote-exit'),
            (rf"(lp:)((?=[A-Za-z_]){constant_re})", bygroups(Number, Name.Variable)),
            (r"(lp:\()([A-Za-z]+)( )([^)]*)(\))", bygroups(Number, Name.Variable, Text.Whitespace, Text, Number)),
            (r"((?!lp:|\}\})(.|\n))+", using(RocqLexer)),
        ],
        'elpi-quote-exit': [
            include('elpi'),
            (r'\}\}', Punctuation, '#pop'),
        ],
        'elpi-spill': [
            (r'\{[^\{]', Text, '#push'),
            (r'\}[^\}]', Text, '#pop'),
            include('elpi'),
        ],
        'elpi-in-parens': [
            (r"\(", Punctuation, '#push'),
            include('elpi'),
            (r"\)", Punctuation, '#pop'),
        ],
    }
