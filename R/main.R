#### HELPERS

#' Check problem consistency
#'
#' This function allows to check consistency of a problem.
#' 
#' @param problem Problem to check. 
#' @return \code{TRUE} if a model of a problem is feasible and \code{FALSE}
#' if infeasible.
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' isConsistent <- checkConsistency(problem)
#' @export
checkConsistency <- function(problem) {
  model <- buildModel(problem, TRUE)
  return (isModelConsistent(model))
}

checkRelation <- function(model, alternative, class, necessary) {
  stopifnot(!is.null(model$epsilonIndex))
  
  if (necessary) {
    if (class == 1) {
      additionalConstraints <- buildLBAssignmentsConstraint(alternative, 2, model)
    } else if (class == model$nrClasses) {
      additionalConstraints <- buildUBAssignmentsConstraint(alternative, model$nrClasses - 1, model)
    } else if (class > 1 && class < problem$nrClasses) {
      model$constraints <- addVarialbesToModel(model$constraints, c("B", "B"))
      nrVariables <- ncol(model$constraints$lhs)
      
      constrLB <- buildLBAssignmentsConstraint(alternative, class + 1, model)
      constrUB <- buildUBAssignmentsConstraint(alternative, class - 1, model)
      constrRel <- list(lhs = rep(0, nrVariables), dir = "==", rhs = 1)
      
      constrLB$lhs[nrVariables - 1] <- RORUTADIS_BIGM
      constrUB$lhs[nrVariables] <- -RORUTADIS_BIGM
      constrRel$lhs[nrVariables - 1] <- 1
      constrRel$lhs[nrVariables] <- 1
      
      additionalConstraints <- combineConstraints(constrLB, constrUB, constrRel)
    }
  } else { # possible    
    if (class > 1) {
      additionalConstraints <- buildLBAssignmentsConstraint(alternative, class, model)
    }
    
    if (class < model$nrClasses) {
      additionalConstraints <- buildUBAssignmentsConstraint(alternative, class, model)
    }
  }
  
  model$constraints <- combineConstraints(model$constraints, additionalConstraints)
  optimizedEpsilon <- maximizeEpsilon(model)
  
  if (necessary) {
    return (optimizedEpsilon$status != 0 || optimizedEpsilon$optimum < RORUTADIS_MINEPS)
  } else {
    return (optimizedEpsilon$status == 0 && optimizedEpsilon$optimum >= RORUTADIS_MINEPS)
  }
}

checkClassCardinality <- function(class, maximum, nrAlternatives, nrClasses,
                                  model, firstClAsgnBinVarIndex) {
  obj <- rep(0, ncol(model$lhs))
  for(alternative in 0:(nrAlternatives - 1)) {
    index <- firstClAsgnBinVarIndex + alternative * nrClasses + class - 1
    obj[index]  <- 1
  }
  ret <- Rglpk_solve_LP(obj, model$lhs, model$dir, model$rhs, max = maximum,
                        types = model$types)
  rm(model)
  gc()
  return (ret$optimum)
}

#### MAIN PUBLIC FUNCTIONS

#' Calculate assignments
#'
#' This function calculates possible and necessary assignments.
#'
#' @param problem Problem for which assignments will be calculated.
#' @param necessary Whether necessary or possible assignments. 
#' @return \emph{n} x \emph{p} logical matrix, where each row represents one
#' of \emph{n} alternatives and each column represents one of \emph{p} classes.
#' Element \code{[i, h]} is \code{TRUE} if:
#' \itemize{
#' \item for necessary assignments: alternative \code{a_i} is always assigned to
#' class \code{C_h},
#' \item for possible assignments: alternative \code{a_i} can be assigned
#' to class \code{C_h}.
#' }
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' possibleAssignments <- calculateAssignments(problem, FALSE)
#' necessaryAssignments <- calculateAssignments(problem, TRUE)
#' @export
calculateAssignments <- function(problem, necessary) {
  if (!checkConsistency(problem))
    stop("Model infeasible.")
  
  baseModel <- buildModel(problem, T)
  rel <- matrix(nrow = nrow(problem$perf), ncol = problem$nrClasses)
  
  for (alternative in seq_len(nrow(problem$perf))) {
    for(class in seq_len(ncol(problem$perf))) {
      rel[alternative, class] <- checkRelation(model, alternative, class, necessary)
      if (RORUTADIS_VERBOSE) print (paste("relation ", alternative, class, "is", rel[alternative, class]))
    }
  }
  
  if (!is.null(rownames(problem$perf)))
    rownames(rel) <- rownames(problem$perf)
  
  return (rel)
}

#' Compare assignments
#'
#' This function compares assignments. In this version of the package only necessary
#' assignments are supported.
#'
#' @param problem Problem for which assignments will be compared.
#' @param necessary Whether necessary or possible assignments. 
#' @return \emph{n} x \emph{n} logical matrix, where \code{n} is a number of
#' alternatives. Cell \code{[i, j]} is \code{TRUE} if \emph{a_i} is assigned to
#' class at least as good as class of \emph{a_j} for all compatible value
#' functions for necessary assignments or for at least one compatible value function
#' for possible assignments.
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' resultOfComparison <- compareAssignments(problem)
#' @export
compareAssignments <- function(problem, necessary = TRUE) {
  if (necessary == FALSE) {
    stop("Comparing possible assignments not supported.")
  }
  
  nrAlternatives <- nrow(problem$perf)
  altVars <- buildAltVariableMatrix(problem$perf)
  baseModel <- buildBaseModel(problem)
  epsilonIndex <- ncol(altVars)
  firstThresholdIndex <- ncol(altVars) + sum(getNrLinearSegments(problem$characteristicPoints)) + 1
  lastThresholdIndex <- firstThresholdIndex + problem$nrClasses - 2
  
  for (i in 1:(ncol(baseModel$lhs) - epsilonIndex))
    altVars <- cbind(altVars, 0)
  
  result <- matrix(nrow = nrAlternatives, ncol = nrAlternatives)
  
  for (i in 1:nrAlternatives) {
    for (j in 1:nrAlternatives) {
      result[i, j] <- TRUE
      
      for (class in 1:(problem$nrClasses - 1)) {
        constraintForI <- buildUBAssignmentsConstraint(i, class, altVars, firstThresholdIndex,
                                                       lastThresholdIndex, epsilonIndex)
        constraintForJ <- buildLBAssignmentsConstraint(j, class + 1, altVars, firstThresholdIndex,
                                                       lastThresholdIndex)
        
        newModel <- combineConstraints(baseModel, constraintForI, constraintForJ)
        
        ret <- maximizeEpsilon(newModel, epsilonIndex)
        
        if (ret$status == 0 && ret$optimum >= RORUTADIS_MINEPS) {
          result[i, j] <- FALSE
          break
        }
      }
      
      if (RORUTADIS_VERBOSE) print (paste("It is ", result[i, j], " that alternative ",
                                          i, " is always in at least as good class as class of alternative ",
                                          j, ".", sep = ""))
    }
  }
  
  return (result)
}

#' Calculate extreme class cardinalities
#'
#' This function calculates minimal and maximal possible cardinality
#' of each class.
#'
#' @param problem Problem for which extreme class cardinalities will be calculated.
#' @return \emph{p} x \emph{2} matrix, where \emph{p} is the number of classes.
#' Value at \code{[h, 1]} is a minimal possible cardinality of class \code{C_h},
#' and value at \code{[h, 2]} is a maximal possible cardinality of class \code{C_h}.
#' @seealso
#' \code{\link{addMinimalClassCardinalities}}
#' \code{\link{addMaximalClassCardinalities}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' extremeClassCardinalities <- calculateExtremeClassCardinalities(problem)
#' @export
calculateExtremeClassCardinalities <- function(problem) {
  if (!checkConsistency(problem))
    stop("Model infeasible.")
  
  baseModel <- buildBaseModel(problem, isEpsilonStrictyPositive = TRUE)
  nrAlternatives <- nrow(problem$perf)
  firstClAsgnBinVarIndex <- getFirstClAsgnBinVarIndex(problem)
  rel <- matrix(nrow = problem$nrClasses, ncol = 2)
  
  for(class in 1:problem$nrClasses) {
    rel[class, 1] <- checkClassCardinality(class, FALSE, nrAlternatives,
                                           problem$nrClasses, baseModel, firstClAsgnBinVarIndex)
    if (RORUTADIS_VERBOSE) print (paste("minimal cardinality of class ", class, "equals", rel[class, 1]))
    
    rel[class, 2] <- checkClassCardinality(class, TRUE, nrAlternatives,
                                           problem$nrClasses, baseModel, firstClAsgnBinVarIndex)
    if (RORUTADIS_VERBOSE) print (paste("maximal cardinality of class ", class, "equals", rel[class, 2]))
  }
  
  return (rel)
}

#' Merge different assignments
#'
#' This function allows to merge different assignments, e.g. from various
#' decision makers (group result, group assignment).
#' There are four types of group assignments:
#' \itemize{
#' \item \strong{P}ossible \strong{P}ossible -
#' alternative \emph{a_i} is \strong{possibly} in class \emph{C_h}
#' \strong{for at least one} decision maker,
#' \item \strong{P}ossible \strong{N}ecessary - 
#' alternative \emph{a_i} is \strong{possibly} in class \emph{C_h}
#' \strong{for all} decision makers,
#' \item \strong{N}ecessary \strong{P}ossible - 
#' alternative \emph{a_i} is \strong{necessarily} in class \emph{C_h}
#' \strong{for at least one} decision maker,
#' \item \strong{N}ecessary \strong{N}ecessary - 
#' alternative \emph{a_i} is \strong{necessarily} in class \emph{C_h}
#' \strong{for all} decision makers.
#' }
#' The first possible-necessary parameter depends on decision makers
#' assignments computed earlier, and the second is define as function parameter.
#' 
#' @param assignmentList List of assignment matrices (results of calling
#' \code{\link{calculateAssignments}} function).
#' @param necessary Whether necessary or possible merging.
#' @return \emph{n} x \emph{p} logical matrix, where each row represents one
#' of \emph{n} alternatives and each column represents one of \emph{p} classes.
#' Element \code{[i, h]} is \code{TRUE} if alternative \code{a_i} can be assigned
#' to class \code{C_h}.
#' @seealso
#' \code{\link{calculateAssignments}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' DM1Problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' DM2Problem <- addAssignmentsLB(problem, c(2, 2), c(4, 2))
#' 
#' necessary <- FALSE
#' assignmentList <- list()
#' assignmentList[[1]] <- calculateAssignments(DM1Problem, necessary)
#' assignmentList[[2]] <- calculateAssignments(DM2Problem, necessary)
#' 
#' # generate possible - necessary assignments
#' PNAssignments <- mergeAssignments(assignmentList, TRUE)
#' @export
mergeAssignments <- function(assignmentList, necessary) {
  stopifnot(is.list(assignmentList))
  stopifnot(length(assignmentList) > 0)
  stopifnot(is.logical(necessary))
  
  if (length(assignmentList) == 1)
    return (assignmentList[1])
  
  result <- assignmentList[[1]]
  
  if (necessary) {
    for (k in 2:length(assignmentList)) {
      for (h in 1:ncol(result)) {
        for (i in 1:nrow(result)) {
          result[i, h] <- result[i, h] && assignmentList[[k]][i, h]
        }
      }
    }
  }
  else {
    for (k in 2:length(assignmentList)) {
      for (h in 1:ncol(result)) {
        for (i in 1:nrow(result)) {
          result[i, h] <- result[i, h] || assignmentList[[k]][i, h]
        }
      }
    }
  }
  
  return (result)
}

#' Find representative utility function
#'
#' This function finds a representative utility function for a problem.
#' 
#' @param problem Problem to investigate.
#' @param mode An integer that represents a method of a computing representative
#' utility function:
#' \itemize{
#' \item \code{0} - iterative mode,
#' \item \code{1} - compromise mode.
#' }
#' @param relation A matrix of assignment pairwise comparisons. Can be provided if
#' it has been calculated earlier (with \code{\link{compareAssignments}}). If
#' the parameter is \code{NULL}, it will be computed.
#' @return This function returns a result of solving model of a problem. It can be
#' used for further computations (e.g. \code{\link{getThresholds}},
#' \code{\link{getMarginalUtilities}}, \code{\link{getCharacteristicPoints}}). If representative utility function was
#' not found, the function returns \code{NULL}.
#' @seealso
#' \code{\link{getCharacteristicPoints}}
#' \code{\link{getMarginalUtilities}} 
#' \code{\link{getThresholds}}
#' @examples
#' perf <- matrix(c(5, 2, 1, 7, 0.5, 0.9, 0.4, 0.4), ncol = 2)
#' problem <- buildProblem(perf, 3, FALSE, c('g', 'g'), c(0, 0))
#' problem <- addAssignmentsLB(problem, c(1, 2), c(2, 3))
#' 
#' representativeFunction <- findRepresentativeFunction(problem, 0)
#' thresholds <- getThresholds(problem, representativeFunction)
#' @export
findRepresentativeFunction <- function(problem, mode, relation = NULL) {
  stopifnot(mode == 0 || mode == 1)
  
  if (is.null(relation)) {
    relation <- compareAssignments(problem)
  }
  
  model <- buildBaseModel(problem, TRUE)
  nrAlternatives <- nrow(problem$perf)
  altVars <- buildAltVariableMatrix(problem$perf)
  
  if (mode == 0) {
    # iterative mode
    
    deltaIndex <- ncol(model$lhs) + 1
    gammaIndex <- ncol(model$lhs) + 3
    model <- addVarialbesToModel(model, c("C", "C", "C", "C"))
    
    for (i in 1:(nrAlternatives - 1)) {
      for (j in (i + 1):nrAlternatives) {
        if (relation[i, j] && !relation[j, i]) {
          #U(a_i) - U(a_j) >= delta
          newConstraint <- buildUtilityDifferenceConstraint(i, j, altVars, ncol(model$lhs))
          newConstraint[deltaIndex] <- -1
          newConstraint[deltaIndex + 1] <- 1
          model <- combineConstraints(model, list(lhs = newConstraint, dir = ">=", rhs = 0))
        }
        else if (!relation[i, j] && relation[j, i]) {
          #U(a_j) - U(a_i) >= delta
          newConstraint <- buildUtilityDifferenceConstraint(j, i, altVars, ncol(model$lhs))
          newConstraint[deltaIndex] <- -1
          newConstraint[deltaIndex + 1] <- 1
          model <- combineConstraints(model, list(lhs = newConstraint, dir = ">=", rhs = 0))
        }
      }
    }
    
    obj <- rep(0, ncol(model$lhs))
    obj[deltaIndex] <- 1  
    obj[deltaIndex + 1] <- -1 
    solution <-  Rglpk_solve_LP(obj, model$lhs, model$dir, model$rhs,
                                max = TRUE, types = model$types)
    
    if (solution$status != 0) {
      return (NULL)
    }
    
    if (solution$optimum < 0) {
      warning(paste("Solution was found, but the optimization target is negative (", solution$optimum, ").", sep = ""))
    }
    
    newConstraint <- rep(0, ncol(model$lhs))
    newConstraint[deltaIndex] <- 1
    newConstraint[deltaIndex + 1] <- -1
    model <- combineConstraints(model, list(lhs = newConstraint,
                                            dir = "==",
                                            rhs = solution$optimum))
    # print (solution$optimum)
    
    for (i in 1:(nrAlternatives - 1)) {
      for (j in (i + 1):nrAlternatives) {
        if (relation[i, j] == relation[j, i]) {
          #U(a_i) - U(a_j) <= gamma
          #U(a_j) - U(a_i) <= gamma
          newConstraint <- buildUtilityDifferenceConstraint(i, j, altVars, ncol(model$lhs))
          newConstraint[gammaIndex] <- -1
          newConstraint[gammaIndex + 1] <- 1
          model <- combineConstraints(model, list(lhs = newConstraint, dir = "<=", rhs = 0))
          newConstraint <- buildUtilityDifferenceConstraint(j, i, altVars, ncol(model$lhs))
          newConstraint[gammaIndex] <- -1
          newConstraint[gammaIndex + 1] <- 1
          model <- combineConstraints(model, list(lhs = newConstraint, dir = "<=", rhs = 0))
        }
      }
    }
    
    obj <- rep(0, ncol(model$lhs))
    obj[gammaIndex] <- 1  
    obj[gammaIndex + 1] <- -1 
    solution <- Rglpk_solve_LP(obj, model$lhs, model$dir, model$rhs,
                              max = FALSE, types = model$types)
    
    if (solution$status != 0) {
      return (NULL)
    }
    
    if (solution$optimum < 0) {
      warning(paste("Solution was found, but the optimization target is negative (", solution$optimum, ").", sep = ""))
    }
    
    return (solution)
  }
  else if (mode == 1) {
    # compromise mode
    
    deltaIndex <- ncol(model$lhs) + 1
    model <- addVarialbesToModel(model, c("C", "C"))
    altVars <- buildAltVariableMatrix(problem$perf)
    different <- c()
    similar <- c()
    
    for (i in 1:(nrAlternatives - 1)) {
      for (j in (i + 1):nrAlternatives) {
        if (relation[i, j] && !relation[j, i]) {
          different <- c(different, i, j)
        }
        else if (!relation[i, j] && relation[j, i]) {
          different <- c(different, j, i)
        }
        else {
          similar <- c(similar, i, j)
        }
      }
    }
    
    if (length(similar) == 0 || length(different) == 0) {
      stop("Compromise mode (1) does not work in this case. Try with another mode.")
    }
    
    for (i in seq(1, length(different), by = 2)) {
      for (j in seq(1, length(similar), by = 2)) {
        newConstraint <- buildUtilityMultipleDifferenceConstraint(different[i],
                                                                  different[i + 1],
                                                                  similar[j],
                                                                  similar[j + 1], 
                                                                  altVars,
                                                                  ncol(model$lhs))
        newConstraint[deltaIndex] <- -1
        newConstraint[deltaIndex + 1] <- 1
        model <- combineConstraints(model, list(lhs = newConstraint, dir = ">=", rhs = 0))
      }
    }
    
    obj <- rep(0, ncol(model$lhs))
    obj[deltaIndex] <- 1  
    obj[deltaIndex + 1] <- -1 
    solution <- Rglpk_solve_LP(obj, model$lhs, model$dir, model$rhs,
                               max = TRUE, types = model$types)
    
    if (solution$status != 0) {
      return (NULL)
    }
    
    if (solution$optimum < 0) {
      warning(paste("Solution was found, but the optimization target is negative (", solution$optimum, ").", sep = ""))
    }
    
    return (solution)
  }
}

# todo: documentation of findFunciton

#' @export
findFunction <- function(problem) {
  model <- buildModel(problem, TRUE)
  solution <- maximizeEpsilon(model)
  
  if (solution$status == 0 && solution$optimum >= RORUTADIS_MINEPS) {
    return (solution)
  }
  
  return (NULL)
}

