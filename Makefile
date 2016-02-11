
thesis/snippets.tex: output/document/Snippets.tex
	sed -n '/\\snip{/,/endsnip/p' output/document/Snippets.tex > thesis/snippets.tex

output/document/Snippets.tex: thesis/Snippets.thy ROOT
	isabelle build -D .
