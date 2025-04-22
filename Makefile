STRING1 = "Last updated on "
STRING2 = <script async src='https://www.googletagmanager.com/gtag/js?id=G-3789HN6BVW'></script>
STRING3 = <script>window.dataLayer = window.dataLayer || [];function gtag(){dataLayer.push(arguments);}gtag('js', new Date());gtag('config', 'G-3789HN6BVW');</script>


RESOURCEDIR = "resources"
TARGETDIR = "build"


SOURCES = $(wildcard *.md)
HTMLs = $(patsubst %.md,build/%.html,$(SOURCES))
TEMPFILE = build/sdfgsdfs7fs8d7tfgsduifgsdi5234j

all: mkdir copy_resources $(HTMLs)

mkdir:
	mkdir -p $(TARGETDIR)

copy_resources:
	cp -r $(RESOURCEDIR) $(TARGETDIR)

build/%.html: %.md
	cat $< > $(TEMPFILE)
	echo "\n\\ \n\n\\ \n\n***\n\n<span class="footer">*$(STRING1) `stat -c %Y Makefile  | date +'%b %d, %Y'`. </span> $(STRING2) $(STRING3)" >> $(TEMPFILE)
	pandoc --mathjax -t html5 -s -c $(RESOURCEDIR)/style.css $(TEMPFILE) -o $@
	rm -f $(TEMPFILE)

clean: 
	rm -rf $(TARGETDIR)
