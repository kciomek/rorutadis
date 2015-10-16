###### ASSIGNEMNT EXAMPLES

buildLBAssignmentsConstraint <- function(alternative, atLeastToClass, model) {
  if (atLeastToClass <= 1 || atLeastToClass > model$nrClasses)
    return (NULL)
  
  lhs <- ua(alternative, ncol(model$constraints$lhs), model$perfToModelVariables)
  lhs[model$firstThresholdIndex + atLeastToClass - 2] <- -1
  
  return (list(lhs = lhs, dir = ">=", rhs = 0))
}

buildUBAssignmentsConstraint <- function(alternative, atMostToClass, model) {
  if (atMostToClass < 1 || atMostToClass >= model$nrClasses)
    return (NULL)
  
  rhs <- 0
  lhs <- ua(alternative, ncol(model$constraints$lhs), model$perfToModelVariables)
  lhs[model$firstThresholdIndex + atMostToClass - 1] <- -1
  
  if (is.null(model$epsilonIndex)) {
    rhs <- -RORUTADIS_MINEPS
  } else {
    lhs[model$epsilonIndex] <- 1
  }
  
  return (list(lhs = lhs, dir = "<=", rhs = rhs))
}

###### PAIRWISE COMPARISIONS

buildAssignmentPairwiseAtLeastComparisonsConstraints <- function(alternativeA,
                                                                 alternativeB,
                                                                 k,
                                                                 model) {
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex - k + 1)) {
    ta <- firstThresholdIndex + i + k - 1
    tb <- firstThresholdIndex + i
    if (ta >= firstThresholdIndex) {
      lhs <- altVars[alternativeA, ]
      lhs[ta] <- -1
      lhs[firstBinaryVarIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData, 0)
    }
    
    if (tb <= lastThresholdIndex) {
      lhs <- altVars[alternativeB, ]
      lhs[epsilonIndex] <- 1
      lhs[tb] <- -1
      lhs[firstBinaryVarIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, 0)
    }
    
    sumLhs[firstBinaryVarIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "<=")
  rhsData <- c(rhsData, lastThresholdIndex - firstThresholdIndex - k + 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

buildassignmentPairwiseAtMostComparisonsConstraints <- function(alternativeA,
                                                                alternativeB,
                                                                l,
                                                                altVars,
                                                                firstThresholdIndex,
                                                                lastThresholdIndex,
                                                                firstBinaryVarIndex,
                                                                epsilonIndex) {
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex - l + 1)) {
    ta <- firstThresholdIndex + i + l
    tb <- firstThresholdIndex + i - 1
    if (ta <= lastThresholdIndex) {
      lhs <- altVars[alternativeA, ]
      lhs[epsilonIndex] <- 1
      lhs[ta] <- -1
      lhs[firstBinaryVarIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, 0)
    }
    
    if (tb >= firstThresholdIndex) {
      lhs <- altVars[alternativeB, ]
      lhs[tb] <- -1
      lhs[firstBinaryVarIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData, 0)
    }
    
    sumLhs[firstBinaryVarIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "<=")
  rhsData <- c(rhsData, lastThresholdIndex - firstThresholdIndex - l + 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

###### DESIRED CLASS CARDINALITIES

buildClassCardinalitieLBConstraint <- function(class,
                                               min,
                                               nrAlternatives,
                                               nrClasses,
                                               firstIndex) {
  lhs <- rep(0, firstIndex + nrAlternatives * nrClasses - 1)
  for (i in seq(firstIndex + class - 1,
                firstIndex + nrAlternatives * nrClasses - 1, by = nrClasses)) {
    lhs[i] <- 1
  }
  
  return (list(lhs = lhs, dir = ">=", rhs = min))
}

buildClassCardinalitieUBConstraint <- function(class,
                                               max,
                                               nrAlternatives,
                                               nrClasses,
                                               firstIndex) {
  lhs <- rep(0, firstIndex + nrAlternatives * nrClasses - 1)
  
  for (i in seq(firstIndex + class - 1,
                firstIndex + nrAlternatives * nrClasses - 1, by = nrClasses)) {
    lhs[i] <- 1
  }
  
  return (list(lhs = lhs, dir = "<=", rhs = max))
}
###### ADDING CONSTRAINT TO MODEL FOR IMPROVEMENT AND DETERIORATION ASSIGNMENT

addAlternativeThresholdComparisionConstraint <- function(alternative,
                                                         threshold,
                                                         model,
                                                         altVars,
                                                         necessary,
                                                         firstThresholdIndex,
                                                         lastThresholdIndex,
                                                         uxIndex = NULL) {
  if (threshold < 1 || threshold > lastThresholdIndex - firstThresholdIndex + 1)
    return (model)
  
  lhs <- altVars[alternative, ]  
  lhs <- c(lhs, rep(0, ncol(model$lhs) - ncol(altVars)))
  lhs[firstThresholdIndex + threshold - 1] <- -1
  
  dir <- NULL
  if (necessary) dir <- "<="
  else dir <- ">="
  
  if (!is.null(uxIndex)) {
    lhs[uxIndex] <- 1
    lhs[uxIndex + 1] <- -1
  }
  
  return (combineConstraints(model, list(lhs = lhs, dir = dir, rhs = 0)))
}

#### HELPERS

addVarialbesToModel <- function(constraints, variables) {
  for (var in variables)
    constraints$lhs <- cbind(constraints$lhs, 0)
  constraints$types <- c(constraints$types, variables)
  return (constraints)
}

extendModelWithAssignmentVariables <- function(model) {
  nrAlternatives <- nrow(model$perfToModelVariables)
  nrClasses <- model$nrClasses
  
  firstBinaryVariableIndex <- ncol(model$constraints$lhs) + 1
  
  model$constraints <- addVarialbesToModel(model$constraints, rep("B", nrAlternatives * model$nrClasses))
  nrVariables <- ncol(model$constraints$lhs)
  
  for (i in seq_len(nrAlternatives)) {
    for (h in seq_len(nrClasses)) {        
      if (h > 1) {
        lhs <- ua(i, nrVariables, model$perfToModelVariables)
        lhs[model$firstThresholdIndex + h - 2] <- -1
        lhs[firstBinaryVariableIndex + (i - 1) * nrClasses + h - 1] <- -RORUTADIS_BIGM
        
        model$constraints <- combineConstraints(model$constraints,
                                                list(lhs = lhs, dir = ">=", rhs = -RORUTADIS_BIGM))
      }
      
      if (h < nrClasses) {
        lhs <- ua(i, nrVariables, model$perfToModelVariables)
        rhs <- 0
        lhs[model$firstThresholdIndex + h - 1] <- -1
        
        if (is.null(model$epsilonIndex)) {
          rhs <- -RORUTADIS_MINEPS
        } else {
          lhs[model$epsilonIndex] <- 1
        }
        
        lhs[firstBinaryVariableIndex + (i - 1) * nrClasses + h - 1] <- RORUTADIS_BIGM
        
        model$constraints <- combineConstraints(model$constraints,
                                                list(lhs = lhs, dir = "<=", rhs = RORUTADIS_BIGM + rhs))
      }
    }
    
    lhs <- rep(0, nrVariables)
    lhs[(firstBinaryVariableIndex + (i - 1) * nrClasses):(firstBinaryVariableIndex + i * nrClasses - 1)] <- 1
    
    model$constraints <- combineConstraints(model$constraints,
                                            list(lhs = lhs, dir = "==", rhs = 1))
  }
  
  return (model)
}

combineConstraints <- function(...) {
  allConst <- list(...)
  
  lhs <- c()
  dir <- c()
  rhs <- c()
  types <- c()
  
  for (const in allConst) {
    if (!is.null(const)) {      
      lhs <- rbind(lhs, const$lhs)
      dir <- c(dir, const$dir)
      rhs <- c(rhs, const$rhs)
      types <- c(types, const$types)
    }
  }
  
  return (list(lhs = lhs, dir = dir, rhs = rhs, types = types))
}

removeConstraints <- function(allConst, constraintsToRemoveIndices) {
  return (list(lhs = allConst$lhs[-c(constraintsToRemoveIndices), ],
               dir = allConst$dir[-c(constraintsToRemoveIndices)],
               rhs = allConst$rhs[-c(constraintsToRemoveIndices)],
               types = allConst$types))
}

#### BUILDING MODEL

buildModel <- function(problem, includeEpsilonAsVariable) {  
  nrAlternatives <- nrow(problem$perf)
  nrCriteria <- ncol(problem$perf)
  
  # criterion value to alternative indices
  
  criterionValues <- replicate(nrCriteria, list())
  
  for (j in seq_len(nrCriteria)) {
    for (i in seq_len(nrAlternatives)) {
      value <- problem$perf[i, j]
      
      found <- FALSE
      
      for (k in seq_len(length(criterionValues[[j]]))) {
        if (criterionValues[[j]][[k]]$value == value) { # todo: consider epsilon
          found <- TRUE
          criterionValues[[j]][[k]]$alternatives <- c(criterionValues[[j]][[k]]$alternatives, i)
        }
      }
      
      if (!found) {
        criterionValues[[j]][[length(criterionValues[[j]]) + 1]] <- list(
          value=value,
          alternatives=c(i)
        )
      }
    }
    
    if (length(criterionValues[[j]]) < 2) {
      stop(paste("Criterion ", j, " is superfluous!"))
    }
    
    # sort criterion values
    criterionValues[[j]] <- criterionValues[[j]][order(
      sapply(criterionValues[[j]],
             function(x) x$value, simplify=TRUE
             ), decreasing=FALSE)]
  }
  
  perfToModelVariables <- replicate(nrCriteria, replicate(nrAlternatives, list()))
  firstChPointVariableIndex <- c(1)
  chPoints <- c()
  
  for (j in seq_len(nrCriteria)) {
    numberOfCharacteristicPoints <- problem$characteristicPoints[j]
    
    if (numberOfCharacteristicPoints == 0) {
      numberOfCharacteristicPoints <- length(criterionValues[[j]])
    }
    
    if (j != nrCriteria) {
      firstChPointVariableIndex[j + 1] <- firstChPointVariableIndex[j] + numberOfCharacteristicPoints - 1
    }
    
    chPoints[j] <- numberOfCharacteristicPoints
  }
  
  numberOfVariables <- firstChPointVariableIndex[length(firstChPointVariableIndex)] + chPoints[nrCriteria] - 2
  
  for (j in seq_len(nrCriteria)) {
    firstValue <- criterionValues[[j]][[1]]$value
    lastValue <- criterionValues[[j]][[length(criterionValues[[j]])]]$value
    direction <- problem$criteria[j]
    
    if (problem$characteristicPoints[j] == 0) {      
      for (i in seq_len(nrAlternatives)) {
        value <- problem$perf[i, j]
        criterionValueIndex <- which(sapply(criterionValues[[j]], function(x){x$value == value}))
        
        if (direction == "g" && criterionValueIndex > 1) {
          perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + criterionValueIndex - 2, 1.0)
        } else if (direction == "c" && criterionValueIndex < length(criterionValues[[j]])) {
          perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + criterionValueIndex - 1, 1.0)
        }
      }
    } else {
      numberOfCharacteristicPoints <- problem$characteristicPoints[j]
      intervalLength <- (lastValue - firstValue) / (numberOfCharacteristicPoints - 1);
      coeff <- 1.0 / intervalLength;
      
      for (i in seq_len(nrAlternatives)) {
        value <- problem$perf[i, j]
        
        if (direction == "g") {
          if (value == lastValue) {
            perfToModelVariables[[i, j]][[1]] <- c(firstChPointVariableIndex[j] + numberOfCharacteristicPoints - 2, 1.0)
          } else if (value > firstValue) {
            lowerChPointIndex <- floor((value - firstValue) * coeff)
            
            if (lowerChPointIndex >= numberOfCharacteristicPoints - 1) {
              stop("InternalError?: lowerChPointIndex >= numberOfCharacteristicPoints - 1: This should never happen.");
            }
            
            lowerValue = firstValue + intervalLength * lowerChPointIndex
            upperValue = firstValue + intervalLength * (lowerChPointIndex + 1)
            
            lowerCoeff <- 0.0
            upperCoeff <- 0.0
            
            if (value <= lowerValue) {
              # comp accuracy
              lowerCoeff = 1.0
              upperCoeff = 0.0
            } else if (value >= upperValue) {
              # comp accuracy
              lowerCoeff = 0.0
              upperCoeff = 1.0
            } else {
              lowerCoeff = (lowerValue - value) / (upperValue - lowerValue) + 1.0
              upperCoeff = (value - lowerValue) / (upperValue - lowerValue)
            }
            
            if (lowerChPointIndex > 0) {
              perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + lowerChPointIndex - 1, lowerCoeff)
              perfToModelVariables[[i, j]][[2]] = c(firstChPointVariableIndex[j] + lowerChPointIndex, upperCoeff)
            } else {
              perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + lowerChPointIndex, upperCoeff)
            }
          }
        } else {
          if (value == firstValue) {
            perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j], 1.0)
          } else if (value < lastValue) {
            lowerChPointIndex <- floor((value - firstValue) * coeff)
            
            if (lowerChPointIndex >= numberOfCharacteristicPoints - 1) {
              stop("InternalError?: lowerChPointIndex >= numberOfCharacteristicPoints - 1: This should never happen.");
            }
            
            lowerValue = firstValue + intervalLength * lowerChPointIndex
            upperValue = firstValue + intervalLength * (lowerChPointIndex + 1)
            
            lowerCoeff <- 0.0
            upperCoeff <- 0.0
            
            if (value <= lowerValue) {
              # comp accuracy
              lowerCoeff = 1.0
              upperCoeff = 0.0
            } else if (value >= upperValue) {
              # comp accuracy
              lowerCoeff = 0.0
              upperCoeff = 1.0
            } else {
              lowerCoeff = (upperValue - value) / (upperValue - lowerValue)
              upperCoeff = (value - upperValue) / (upperValue - lowerValue) + 1.0
            }
            
            if (lowerChPointIndex < numberOfCharacteristicPoints - 2) {
              perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + lowerChPointIndex - 1, lowerCoeff)
              perfToModelVariables[[i, j]][[2]] = c(firstChPointVariableIndex[j] + lowerChPointIndex, upperCoeff)
            } else {
              perfToModelVariables[[i, j]][[1]] = c(firstChPointVariableIndex[j] + lowerChPointIndex - 1, lowerCoeff)
            }
          }
        }
      }
    }
  }
  
  # epsilon index
  
  epsilonIndex <- NULL
  if (includeEpsilonAsVariable) {
    numberOfVariables <- numberOfVariables + 1
    epsilonIndex <- numberOfVariables
  }
  
  # threshold indices
  
  firstThresholdIndex <- numberOfVariables + 1  
  numberOfVariables <- numberOfVariables + problem$nrClasses - 1
  
  # constraints
  
  # sum to 1
  
  lhs <- rep(0, numberOfVariables)
  
  for (j in seq_len(nrCriteria)) {
    if (problem$criteria[j] == 'g')
      lhs[firstChPointVariableIndex[j] + chPoints[j] - 2] <- 1
    else
      lhs[firstChPointVariableIndex[j]] <- 1
  }
  
  constraints <- list(lhs = lhs, dir = "==", rhs = 1)
  
  # monotonocity of vf
  
  for (j in seq_len(nrCriteria)) {
    for (k in seq_len(chPoints[j] - 2)) {
      lhs <- rep(0, numberOfVariables)
      rhs <- 0
      
      if (problem$criteria[j] == "g") {
        lhs[firstChPointVariableIndex[j] + k - 1] <- 1
        lhs[firstChPointVariableIndex[j] + k] <- -1
      } else {
        lhs[firstChPointVariableIndex[j] + k - 1] <- -1
        lhs[firstChPointVariableIndex[j] + k] <- 1
      }
      
      if (problem$strictVF) {
        if (includeEpsilonAsVariable) {
          lhs[epsilonIndex] <- 1
        } else {
          rhs <- -RORUTADIS_MINEPS
        }
      }
      
      constraints <- combineConstraints(constraints,
                                        list(lhs = lhs, dir = "<=", rhs = rhs))
    }
    
    lhs <- rep(0, numberOfVariables)
    rhs <- 0
    
    if (problem$criteria[j] == 'g')
      lhs[firstChPointVariableIndex[j] + chPoints[j] - 2] <- -1
    else
      lhs[firstChPointVariableIndex[j]] <- -1
    
    if (problem$strictVF) {
      if (includeEpsilonAsVariable) {
        lhs[epsilonIndex] <- 1
      } else {
        rhs <- -RORUTADIS_MINEPS
      }
    }
    
    constraints <- combineConstraints(constraints,
                                      list(lhs = lhs, dir = "<=", rhs = rhs))
  }
  
  # first threshold over 0
  
  lhs <- rep(0, numberOfVariables)
  rhs <- 0
  
  lhs[firstThresholdIndex] <- -1
  
  if (includeEpsilonAsVariable) {
    lhs[epsilonIndex] <- 1
  } else {
    rhs <- -RORUTADIS_MINEPS
  }
  
  constraints <- combineConstraints(constraints,
                                    list(lhs = lhs, dir = "<=", rhs = rhs))
  
  # last threshold under 1
  
  lhs <- rep(0, numberOfVariables)
  rhs <- 1
  
  lhs[firstThresholdIndex + problem$nrClasses - 2] <- 1
  
  if (includeEpsilonAsVariable) {
    lhs[epsilonIndex] <- 1
  } else {
    rhs <- 1 - RORUTADIS_MINEPS
  }
  
  constraints <- combineConstraints(constraints,
                                    list(lhs = lhs, dir = "<=", rhs = rhs))
  
  for (k in seq_len(problem$nrClasses - 2)) {
    lhs <- rep(0, numberOfVariables)
    rhs <- 0
    
    lhs[firstThresholdIndex + k - 1] <- 1
    lhs[firstThresholdIndex + k] <- -1
    
    if (includeEpsilonAsVariable) {
      lhs[epsilonIndex] <- 1
    } else {
      rhs <- -RORUTADIS_MINEPS
    }
    
    constraints <- combineConstraints(constraints,
                                      list(lhs = lhs, dir = "<=", rhs = rhs))
  }
  
  constraints$types <- rep("C", numberOfVariables)
  
  # building model
  
  model <- list(
    constraints = constraints,
    firstChPointVariableIndex = firstChPointVariableIndex,
    epsilonIndex = epsilonIndex,
    firstThresholdIndex = firstThresholdIndex,
    chPoints = chPoints,
    perfToModelVariables = perfToModelVariables,
    criterionValues = criterionValues,
    criterionPreferenceDirection = problem$criteria,
    prefInfoToConstraints = list(),
    nrClasses = problem$nrClasses,
    generalVF = problem$characteristicPoints == 0
  )
  
  # preference information
  
  # assignment examples
  
  prefInfoIndex <- 1
  
  if (is.matrix(problem$assignmentsLB)) {
    for (k in seq_len(nrow(problem$assignmentsLB))) {
      alternative <- problem$assignmentsLB[k, 1]
      atLeastToClass <- problem$assignmentsLB[k, 2]
            
      model$constraints <- combineConstraints(model$constraints,
                                              buildLBAssignmentsConstraint(alternative, atLeastToClass, model))
      
      model$prefInfoToConstraints[[prefInfoIndex]] <- nrow(model$constraints$lhs)
      prefInfoIndex <- prefInfoIndex + 1
    }
  }

  if (is.matrix(problem$assignmentsUB)) {
    for (k in seq_len(nrow(problem$assignmentsUB))) {
      alternative <- problem$assignmentsUB[k, 1]
      atMostToClass <- problem$assignmentsUB[k, 2]
      
      model$constraints <- combineConstraints(model$constraints,
                                              buildUBAssignmentsConstraint(alternative, atMostToClass, model))
      
      model$prefInfoToConstraints[[prefInfoIndex]] <- nrow(model$constraints$lhs)
      prefInfoIndex <- prefInfoIndex + 1
    }
  }  
  
  if ((is.matrix(problem$assignmentPairwiseAtLeastComparisons) && nrow(problem$assignmentPairwiseAtLeastComparisons) > 0) ||
        (is.matrix(problem$assignmentPairwiseAtMostComparisons) && nrow(problem$assignmentPairwiseAtMostComparisons) > 0) ||
        (is.matrix(problem$minimalClassCardinalities) && nrow(problem$minimalClassCardinalities) > 0) ||
        (is.matrix(problem$maximalClassCardinalities) && nrow(problem$maximalClassCardinalities) > 0)) {
    model <- extendModelWithAssignmentVariables(model)
    
    # assignment-based pairwise comparisons
    
    if (is.matrix(problem$assignmentPairwiseAtLeastComparisons)) {
      for (k in seq_len(nrow(problem$assignmentPairwiseAtLeastComparisons))) {
        #todo
      }
    }
    
    if (is.matrix(problem$assignmentPairwiseAtMostComparisons)) {
      for (k in seq_len(nrow(problem$assignmentPairwiseAtMostComparisons))) {
        #todo
      }
    }    
    
    # desired class cardinalities
    
    if (is.matrix(problem$minimalClassCardinalities)) {
      for (k in seq_len(nrow(problem$minimalClassCardinalities))) {
        #todo
      }
    }
    
    if (is.matrix(problem$maximalClassCardinalities)) {
      for (k in seq_len(nrow(problem$maximalClassCardinalities))) {
        #todo
      }
    }
  }

  return (model)
}

ua <- function(alternative, nrVariables, perfToModelVariables) {
  res <- rep(0, nrVariables)
  
  for (j in seq_len(ncol(perfToModelVariables))) {
    for (k in seq_len(length(perfToModelVariables[[alternative, j]]))) {
      res[perfToModelVariables[[alternative, j]][[k]][1]] <- perfToModelVariables[[alternative, j]][[k]][2]
    }
  }
  
  return (res)
}
