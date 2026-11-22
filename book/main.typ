#import "meat.typ": *

#show: book.with(title: "meat", subtitle: "Information theory")

#include "chapters/shannon.typ"
#include "chapters/source.typ"
#include "chapters/channel.typ"
#include "chapters/network.typ"
#include "chapters/continuous.typ"

#coverage()
