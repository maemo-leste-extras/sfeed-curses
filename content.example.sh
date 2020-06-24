#!/bin/sh
# RSS/Atom content viewer.
#
# Dependencies:
# - awk, sh, etc.
# - lynx or webdump or HTML converting to plain-text.

# content()
content() {
	awk -F '\t' '
function unescape(s) {
	gsub("\\\\t", "\t", s);
	gsub("\\\\n", "\n", s);
	gsub("\\\\\\\\", "\\", s);
	return s;
}
{
	print unescape($4);
	exit;
}'
}

tmp=$(mktemp 'sfeed_curses_XXXXXXXXXX')
trap "rm $tmp" EXIT
cat > "$tmp"

(awk -F '\t' '
{
	print "Title:     " $2;
	if (length($7))
		print "Author:    " $7;
	if (length($3))
		print "Link:      " $3;
	if (length($8))
		print "Enclosure: " $8;
	print "";
	exit;
}' < "$tmp"

contenttype=$(awk -F '\t' '{ print $5; exit }' < "$tmp")
if test x"$contenttype" = x"plain"; then
	content < "$tmp"
else
	(echo "<span>"; content < "$tmp";echo "</span>") | \
		lynx -stdin -dump -underline_links -image_links
#		lynx -stdin -dump -underline_links -list_inline -image_links
#		webdump -a -l -r -w 79
fi
) | \
less -R
