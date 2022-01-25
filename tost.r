# https://reilly-lab.github.io/Equivalence_Tutorial.html
library(equivalence)
library(tidyverse)
library(reshape2)

set.seed(1234)
a <- rnorm(1000, 10, 2)  #1000 observations with a mean of 10 and an SD=2
b <- a
c <- data.frame(a, b)
head(c)

tost(c$a, c$b, epsilon = 1, paired = FALSE, var.equal = TRUE, conf.level = 0.95)
