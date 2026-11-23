#import "meat.typ": *

#show: book.with(title: "meat", subtitle: "Information theory")

#include "chapters/start.typ"
#include "chapters/shannon.typ"
#include "chapters/source.typ"
#include "chapters/channel.typ"
#include "chapters/manyusers.typ"
#include "chapters/network.typ"
#include "chapters/continuous.typ"
#include "chapters/testing.typ"
#include "chapters/exercises.typ"
#include "chapters/open.typ"

#coverage()
