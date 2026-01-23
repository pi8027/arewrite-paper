# To compile the paper: latexmk -pvc arewrite
@default_files = ("arewrite.tex");
$xelatex         = 'xelatex -shell-escape -interaction=nonstopmode';
$xelatex_silent  = 'xelatex -shell-escape -interaction=batchmode';
$pdflatex        = 'pdflatex -shell-escape -interaction=nonstopmode';
$pdflatex_silent = 'pdflatex -shell-escape -interaction=batchmode';
$bibtex          = 'bibtex';
$biber           = 'biber --bblencoding=utf8 -u -U --output_safechars';
$pdf_mode        = 1;
$max_repeat      = 5;
