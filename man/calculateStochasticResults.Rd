% Generated by roxygen2 (4.1.1): do not edit by hand
% Please edit documentation in R/sampling.R
\name{calculateStochasticResults}
\alias{calculateStochasticResults}
\title{Stochastic results}
\usage{
calculateStochasticResults(problem, nrSamples = 100)
}
\arguments{
\item{problem}{A problem to consider.}

\item{nrSamples}{Number of samples. Use more for better quality of results.}
}
\value{
List with the following named elements:
\itemize{
\item \emph{assignments} - \emph{n} x \emph{p} matrix, where \emph{n} is
the number of alternatives and \emph{p} is number of classes; each element
\code{[i, j]} contains the rate of samples, for which alternative \emph{a_i}
was assigned to class \emph{C_j}.
The exact result can be calculated with function \link{calculateAssignments}.
\item \emph{preferenceRelation} - \emph{n} x \emph{n} matrix, where \emph{n} is
the number of alternatives; each element \code{[i, j]} contains the rate
of samples, for which alternative \emph{a_i} was assigned to class at least
as good as class of \emph{a_j}.
The exact result can be calculated with function \link{compareAssignments}.
\item \emph{classCardinalities} - \emph{p} x \emph{(n + 1)} matrix, where \emph{n}
is the number of alternatives and \emph{p} is number of classes; each element
\code{[i, j]} contains the rate of samples, for which \emph{j-1} alternatives
were assigned to class \emph{C_i}. \strong{Note!} first column corresponds to
\strong{0} elements.
The exact result can be calculated with function \link{calculateExtremeClassCardinalities}.
}
}
\description{
The function calculates stochastic results for alternative assignments,
assignment-based preference relation and class cardinalities.
The results are computed by sampling the space of compatible models.
}
\examples{
perf <- matrix(c(2,1,1,2), 2)
problem <- buildProblem(perf, 2, FALSE, c('g', 'g'), c(0, 0))

calculateStochasticResults(problem, 1000)
}
\seealso{
\code{\link{buildProblem}}
\code{\link{calculateAssignments}}
\code{\link{compareAssignments}}
\code{\link{calculateExtremeClassCardinalities}}
}

