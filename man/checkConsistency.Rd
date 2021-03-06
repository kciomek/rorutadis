% Generated by roxygen2 (4.1.1): do not edit by hand
% Please edit documentation in R/main.R
\name{checkConsistency}
\alias{checkConsistency}
\title{Check problem consistency}
\usage{
checkConsistency(problem)
}
\arguments{
\item{problem}{Problem to check.}
}
\value{
\code{TRUE} if a model of a problem is feasible and \code{FALSE}
otherwise.
}
\description{
This function allows to check if preference information is consistent.
}
\examples{
perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))

isConsistent <- checkConsistency(problem)
}

