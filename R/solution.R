#### SOLVING MODEL

#' @import Rglpk
extremizeVariable <- function(constraints, variableIndex, maximize) {
  obj <- rep(0, ncol(constraints$lhs))
  obj[variableIndex] <- 1  
  Rglpk_solve_LP(obj, constraints$lhs, constraints$dir, constraints$rhs, max = maximize,
                 types = constraints$types)
}

maximizeEpsilon <- function(model) {
  stopifnot(!is.null(model$epsilonIndex))
  
  return (extremizeVariable(model$constraints, model$epsilonIndex, TRUE))
}

isModelConsistent <- function(model) {            
  ret <- maximizeEpsilon(model)
  
  return (ret$status == 0 && ret$optimum >= RORUTADIS_MINEPS)
}

toSolution <- function(model, values) {
  nrVariables <- ncol(model$constraints$lhs)
  nrAlternatives <- nrow(model$perfToModelVariables)
  nrCriteria <- ncol(model$perfToModelVariables)
    
  stopifnot(length(values) == nrVariables)
  
  # thresolds
  
  thresholds = values[model$firstThresholdIndex:(model$firstThresholdIndex + problem$nrClasses - 2)]
  
  # assignments
  
  assignments <- c()  
  for (i in seq_len(nrAlternatives)) {
    assignments[i] <- 1
    
    for (h in seq_len(model$nrClasses - 1)) {
      if (sum(ua(i, nrVariables, model$perfToModelVariables) * values) < thresholds[h]) { #todo: consider epsilon
        break
      }
      
      assignements[i] <- assignements[i] + 1
    }
  }
  
  # epsilon
  
  epsilon <- NULL
  
  if (!is.null(model$epsilonIndex)) {
    epsilon <- values[model$epsilonIndex]
  } else {
    epsilon <- RORUTADIS_MINEPS
  }
  
  # vf
  
  vf <- list()
  
  for (j in seq_len(nrCriteria)) {
    nrValues <- length(model$criterionValues[[j]])
    
    if (model$generalVF[j]) {
      x <- sapply(model$criterionValues[[j]], function(w) { w$value })
    } else {
      firstValue <- model$criterionValues[[j]][[1]]$value
      lastValue <- model$criterionValues[[j]][[length(model$criterionValues[[j]])]]$value
      intervalLength <- lastValue - firstValue
      
      x <- c(firstValue,
             sapply(seq_len(model$chPoints[j] - 2), function(w) { firstValue + intervalLength * w }),
             lastValue)
    }
    
    y <- values[model$firstChPointVariableIndex[j] : model$firstChPointVariableIndex[j] + model$chPoints[j] - 2]
    
    if (model$criterionPreferenceDirection[j] == "g") {
      y <- c(0, y)
    } else {
      y <- c(y, 0)
    }
    
    vf[[j]] <- cbind(x, y)
  }
  
  # alternative values
  
  alternativeValues <- matrix(nrow=nrAlternatives, ncol=nrCriteria)
  
  for (i in seq_len(nrAlternatives)) {
    for (j in seq_len(nrCriteria)) {
      alternativeValues[i, j] <- 0
      
      for (k in seq_len(length(model$perfToModelVariables[[i, j]]))) {
        alternativeValues[i, j] <- alternativeValues[i, j] + values[model$perfToModelVariables[[i, j]][[k]][1]] * model$perfToModelVariables[[i, j]][[k]][2]
      }
    }
  }
  
  return (list(
    vf = vf,
    thresholds = thresholds,
    assignments = assignments,
    alternativeValues = alternativeValues,
    solution = values,
    epsilon = epsilon,
    generalVF = model$generalVF
    ))
}

#### SOLUTION

#' Get thresholds
#'
#' This function extracts values of thresholds from solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return Vector containing \code{h-1} thresholds from \code{t_1} to \code{t_h-1}
#' where \code{t_p-1} is lower threshold of class \code{C_p} and \code{h} is
#' number of classes.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' thresholds <- getThresholds(problem, representativeFunction)
#' @export
getThresholds <- function(problem, solution) {
  .Deprecated()
  return (solution$thresholds)
}

#' Get marginal utilities
#'
#' This function extracts alternatives marginal values from model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return A \emph{n} x \emph{m} matrix containing marginal values of \code{n} alternatives
#' on \code{m} criteria.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' marginalUtilities <- getMarginalUtilities(problem, representativeFunction)
#' @export
getMarginalUtilities <- function(problem, solution) {
  .Deprecated()
  return (solution$alternativeValues)
}

#' Get characteristic points
#'
#' This function extracts values of characteristic points from model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return List of \code{m} matrices for each of \code{m} criteria.
#' Each row \code{c(g, u)} of each matrix contains coordinates of a single
#' characteristic point, where \code{g} - evaluation on corresponding criterion,
#' \code{u} - marginal utility.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getAssignments}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' characteristicPoints <- getCharacteristicPoints(problem, representativeFunction)
#' @export
getCharacteristicPoints <- function(problem, solution) {
  .Deprecated()
  return (solution$vf)
}


#' Get assignments
#'
#' This function returns assignments for given model solution.
#' 
#' @param problem Problem whose model was solved.
#' @param solution Result of model solving (e.g. result of
#' \code{\link{findRepresentativeFunction}} or \code{\link{investigateUtility}}).
#' @return Vector of alternative assignments. Each element contains an index
#' of a class that corresponding alternative was assigned to.
#' @seealso
#' \code{\link{findRepresentativeFunction}}
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getMarginalUtilities}}
#' \code{\link{getThresholds}}
#' \code{\link{investigateUtility}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' assignments <- getAssignments(problem, representativeFunction)
#' @export
getAssignments <- function(problem, solution) {
  .Deprecated()
  return (solution$assignments)
}

