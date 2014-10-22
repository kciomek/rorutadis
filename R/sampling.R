#' Stochastic results
#'
#' The function calculates stochastic results for alternative assignments,
#' assignment-based preference relation and class cardinalities.
#' The results are computed by sampling the space of compatible models.
#' 
#' @param problem A problem to consider.
#' @param nrSamples Number of samples. Use more for better quality of results.
#' @return List with the following named elements:
#' \itemize{
#' \item \emph{assignments} - \emph{n} x \emph{p} matrix, where \emph{n} is
#' the number of alternatives and \emph{p} is number of classes; each element
#' \code{[i, j]} contains the rate of samples, for which alternative \emph{a_i}
#' was assigned to class \emph{C_j}.
#' The exact result can be calculated with function \link{calculateAssignments}.
#' \item \emph{preferenceRelation} - \emph{n} x \emph{n} matrix, where \emph{n} is
#' the number of alternatives; each element \code{[i, j]} contains the rate
#' of samples, for which alternative \emph{a_i} was assigned to class at least
#' as good as class of \emph{a_j}.
#' The exact result can be calculated with function \link{compareAssignments}.
#' \item \emph{classCardinalities} - \emph{p} x \emph{(n + 1)} matrix, where \emph{n}
#' is the number of alternatives and \emph{p} is number of classes; each element
#' \code{[i, j]} contains the rate of samples, for which \emph{j-1} alternatives
#' were assigned to class \emph{C_i}. \strong{Note!} first column corresponds to
#' \strong{0} elements.
#' The exact result can be calculated with function \link{calculateExtremeClassCardinalities}.
#' }
#' @seealso
#' \code{\link{buildProblem}}
#' \code{\link{calculateAssignments}}
#' \code{\link{compareAssignments}}
#' \code{\link{calculateExtremeClassCardinalities}}
#' @examples
#' perf <- matrix(c(2,1,1,2), 2)
#' problem <- buildProblem(perf, 2, FALSE, c('g', 'g'), c(0, 0))
#' 
#' calculateStochasticResults(problem, 1000)
#' @import hitandrun
#' @export
calculateStochasticResults <- function(problem, nrSamples = 100) {
  stopifnot(nrSamples > 0)
  
  model <- buildBaseModel(problem)
  epsilonIndex <- getEpsilonIndex(problem)
  ret <- maximizeEpsilon(model, epsilonIndex)
  
  if (!(ret$status == 0 && ret$optimum >= RORUTADIS_MINEPS)) {
    stop("Model infeasible.")
  }
  
  nrAlternatives <- nrow(problem$perf)
  nrCriteria <- ncol(problem$perf)
  nrClasses <- problem$nrClasses
  altVars <- buildAltVariableMatrix(problem$perf)
  
  result <- list(assignments = NULL, preferenceRelation = NULL, classCardinalities = NULL)
  
  result$assignments <- matrix(data = 0, nrow = nrAlternatives, ncol = nrClasses)
  result$preferenceRelation <- matrix(data = 0, nrow = nrAlternatives, ncol = nrAlternatives)
  result$classCardinalities <- matrix(data = 0, nrow = nrClasses, ncol = nrAlternatives + 1)
  
  model <- buildBaseModel(problem, TRUE, FALSE, TRUE)
  model$dir[which(model$dir == "==")] <- "="
  geq <- which(model$dir == ">=")
  
  for (i in geq) {
    model$rhs[i] <- -1 * model$rhs[i]
    model$lhs[i, ] <- -1 * model$lhs[i, ]
  }
  
  model$dir[geq] <- "<="
  names(model)[1] <- "constr"
  model[[4]] <- NULL
  
  simplified <- extractSeparateVariables(model)
  model <- simplified$model
  
  state <- har.init(model, thin.fn = function(n) { ceiling(log(n + 1)/4 * n^3) },
                    thin = NULL, x0.randomize = FALSE, x0.method = "slacklp", x0 = NULL)
  
  producedSamples <- 0
  allGeneratedSamples <- 0
  
  while (producedSamples < nrSamples) {
    harSample <- har.run(state, n.samples = 1)
    state <- harSample$state
    extendedSample <- extendResult(harSample$samples[1, ], simplified$variables, simplified$values)
    thresholds <- getThresholdsFromHarSample(problem, extendedSample)
    assignments <- getAssignmentsFromHarSample(extendedSample,
                                               nrAlternatives,
                                               altVars,
                                               thresholds,
                                               problem$nrClasses)
    allGeneratedSamples <- allGeneratedSamples + 1
    
    if (isAssignmentsValid(problem, assignments)) {
      result$assignments <- addSampleAssignmetnsToResult(result$assignments, assignments)
      
      for (i in seq_len(nrAlternatives)) {
        for (j in i:nrAlternatives) {
          if (i == j) {
            result$preferenceRelation[i, j] <- result$preferenceRelation[i, j] + 1
          }
          else if (assignments[i] == assignments[j]) {
            result$preferenceRelation[i, j] <- result$preferenceRelation[i, j] + 1
            result$preferenceRelation[j, i] <- result$preferenceRelation[j, i] + 1
          }
          else if (assignments[i] > assignments[j]) {
            result$preferenceRelation[i, j] <- result$preferenceRelation[i, j] + 1
          }
          else {
            result$preferenceRelation[j, i] <- result$preferenceRelation[j, i] + 1
          }
        }
      }
      
      cardinalities <- sapply(seq_len(nrClasses), function(h) { length(which(assignments == h)) })
      
      for (h in seq_len(nrClasses)) {
        result$classCardinalities[h, cardinalities[h] + 1] <- result$classCardinalities[h, cardinalities[h] + 1] + 1
      }  
      
      producedSamples <- producedSamples + 1
    }
  }
  
  # print rejection sampling acceptance rate:
  # print (producedSamples / allGeneratedSamples)
  
  result$assignments <- result$assignments / producedSamples
  result$preferenceRelation <- result$preferenceRelation / producedSamples
  result$classCardinalities <- result$classCardinalities / producedSamples
  
  return (result)
}

extractSeparateVariables <- function(model) {
  variables <- c()
  values <- c()
  rowsToRemove <- c()
  
  for (i in seq_len(ncol(model$constr))) {
    nonZeroRows = which(model$constr[, i] != 0)
    
    if (length(nonZeroRows) == 1) {
      # varaible used only one time
      nonZeroColumns <- which(model$constr[nonZeroRows[1], -i] != 0)
      
      if (length(nonZeroColumns) == 0 && model$dir[nonZeroRows[1]] == "=") {
        variables <- c(variables, i)
        values <- c(values, model$rhs[nonZeroRows[1]] / model$constr[nonZeroRows[1], i])
        rowsToRemove <- c(rowsToRemove, nonZeroRows[1])
      }
    }
  }
  
  if (length(variables) > 0) {
    model$constr = model$constr[-rowsToRemove, -variables]
    model$rhs <- model$rhs[-rowsToRemove]
    model$dir <- model$dir[-rowsToRemove]
  }
  
  return (list(model = model, variables = variables, values = values))
}

extendResult <- function(result, variables, values) {  
  extended <- rep(0, length(result) + length(variables))
  
  j <- 1
  k <- 1
  for (i in seq_len(length(extended))) {
    if (j <= length(variables) && variables[j] == i) {
      extended[i] <- values[j]
      j <- j + 1
    } else {
      extended[i] <- result[k]
      k <- k + 1
    }
  }  
  
  return (extended)
}

addSampleAssignmetnsToResult <- function(result, assignments) {
  for (i in seq_len(length(assignments))) {
    result[i, assignments[i]] <- result[i, assignments[i]] + 1
  }
  
  return (result)
}

isAssignmentsValid <- function(problem, assignmentsToCheck) {
  for (i in seq(nrow(problem$assignmentsLB))) {
    a <- problem$assignmentsLB[i, 1]
    
    if (assignmentsToCheck[a] < problem$assignmentsLB[i, 2])
      return (FALSE)
  }
  
  for (i in seq(nrow(problem$assignmentsUB))) {
    a <- problem$assignmentsUB[i, 1]
    
    if (assignmentsToCheck[a] > problem$assignmentsUB[i, 2])
      return (FALSE)
  }
  
  for (i in seq(nrow(problem$assignmentPairwiseAtLeastComparisons))) {
    a <- problem$assignmentPairwiseAtLeastComparisons[i, 1]
    b <- problem$assignmentPairwiseAtLeastComparisons[i, 2]
    
    if (assignmentsToCheck[a] - assignmentsToCheck[b] < 
          problem$assignmentPairwiseAtLeastComparisons[i, 3])
      return (FALSE)
  }
  
  for (i in seq(nrow(problem$assignmentPairwiseAtMostComparisons))) {
    a <- problem$assignmentPairwiseAtMostComparisons[i, 1]
    b <- problem$assignmentPairwiseAtMostComparisons[i, 2]
    
    if (assignmentsToCheck[a] - assignmentsToCheck[b] > 
          problem$assignmentPairwiseAtMostComparisons[i, 3])
      return (FALSE)
  }
  
  for (i in seq(nrow(problem$minimalClassCardinalities))) {
    h <- problem$minimalClassCardinalities[i, 1]
    
    if (length(which(assignmentsToCheck == h)) < problem$minimalClassCardinalities[i, 2])
      return (FALSE)
  }
  
  for (i in seq(nrow(problem$maximalClassCardinalities))) {
    h <- problem$maximalClassCardinalities[i, 1]
    
    if (length(which(assignmentsToCheck == h)) > problem$maximalClassCardinalities[i, 2])
      return (FALSE)
  }
  
  return (TRUE)
}

getThresholdsFromHarSample <- function(problem, sample) {
  firstThresholdIndex <- getFirstThresholdIndex(problem)
  lastThresholdIndex <- getLastThresholdIndex(problem)
  
  return (sample[firstThresholdIndex:lastThresholdIndex])
}

getAssignmentsFromHarSample <- function(sample, nrAlternatives, altVars,
                                        thresholds, nrClasses) {
  assignments <- array(dim = nrAlternatives)
  
  for (i in seq_len(nrAlternatives)) {
    for (h in seq_len(length(thresholds))) {
      if (sum(altVars[i, ] * sample[1:ncol(altVars)]) < thresholds[h]) {
        assignments[i] <- h
        break
      }
    }
    
    if (is.na(assignments[i])) {
      assignments[i] <- nrClasses
    }
  }
  
  return (assignments)
}
