all: MMGLmanual.pdf
MMGLmanual.pdf: MMGLmanual.texi
	texi2pdf --texinfo=@setcontentsaftertitlepage MMGLmanual.texi
MMGLmanual.html: MMGLmanual.texi
	texi2html MMGLmanual.texi
clean:
	rm -rf *.dvi *.aux *.cp *.fn *.fns *.ky *.log *.pg *.toc *.tp *.vr *~
veryclean: clean
	rm -rf MMGLmanual.html MMGLmanual.pdf
