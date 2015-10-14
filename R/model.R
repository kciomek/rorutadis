#### INDICES, NUMBER OF VARIABLES ETC.

getNrAlt <- function(problem) {
  return (nrow(problem$perf))
}

getNrAltVars <- function(problem) {
  return (sum(as.numeric(lapply(getLevels(problem$perf), length))))
}

getEpsilonIndex <- function(problem) {
  return (getNrAltVars(problem) + 1)
}

getFirstCharacteristicPointIndex <- function(problem) {
  if (sum(getNrLinearSegments(problem$characteristicPoints)) == 0)
    stop("There is no characteristic points in this problem.")
  return (getEpsilonIndex(problem) + 1)
}

getFirstThresholdIndex <- function(problem) {
  return (getEpsilonIndex(problem) + sum(getNrLinearSegments(problem$characteristicPoints)) + 1)
}

getLastThresholdIndex <- function(problem) {
  return (getFirstThresholdIndex(problem) + problem$nrClasses - 2)
}

getNrPairAtLeastCompVars <- function(nrClasses, assignmentPairwiseAtLeastComparisons) {
  if (!is.null(assignmentPairwiseAtLeastComparisons)) {
    return (sum(nrClasses - assignmentPairwiseAtLeastComparisons[, 3]))
  }
  else {
    return (0)
  }
}

getNrPairAtMostCompVars <- function(nrClasses, assignmentPairwiseAtMostComparisons) {
  if (!is.null(assignmentPairwiseAtMostComparisons)) {
    return (sum(nrClasses - assignmentPairwiseAtMostComparisons[, 3]))
  }
  else {
    return (0)
  }
}

getNrPairCompBinVars <- function(problem) {
  return (getNrPairAtLeastCompVars(problem$nrClasses,
                                   problem$assignmentPairwiseAtLeastComparisons)
          + getNrPairAtMostCompVars(problem$nrClasses,
                                    problem$assignmentPairwiseAtMostComparisons))
}

getFirstPairCompBinVarIndex <- function(problem) {
  if (getNrPairCompBinVars(problem) == 0)
    stop("There is no pairwice comparisons in this problem.")
  return (getLastThresholdIndex(problem) + 1)
}

getLastPairCompBinVarIndex <- function(problem) {
  return (getFirstPairCompBinVarIndex(problem) + getNrPairCompBinVars(problem) - 1)
}

getFirstClAsgnBinVarIndex <- function(problem) {
  return (getLastThresholdIndex(problem) + getNrPairCompBinVars(problem) + 1)
}

getLastClAsgnBinVarIndex <- function(problem) {
  return (getLastThresholdIndex(problem) + getNrPairCompBinVars(problem) +
            problem$nrClasses * nrow(problem$perf))
}
#### BUILDING MODEL HELPERS

getLevels <- function(perf) {
  res <- list()
  for (i in 1:ncol(perf)) {
    res[[i]] <- sort(unique(perf[, i]))
  }
  return (res)
}

getNrVars <- function(levels) {
  return (sum(as.numeric(lapply(levels, length))) + 1)# + 1 for epsilon
}

getOffsets <- function(levels) {
  x <- cumsum(lapply(levels, length))
  return (c(1, x[1:length(x) - 1] + 1))
}

buildAltVariableMatrix <- function(perf) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrAlts <- nrow(perf)
  nrCrit <- ncol(perf)
  nrVars <- getNrVars(levels)
  resMat <- matrix(nrow = nrAlts, ncol = nrVars)
  
  for (i in seq_len(nrAlts)) {
    vec <- array(0, dim = nrVars)
    indices <- sapply(1:nrCrit, function(x) { which(levels[[x]] == perf[i, x]) })
    vec[indices + offsets - 1] <- 1
    resMat[i, ] <- vec
  }
  
  return (resMat)
}

addVarialbesToModel <- function(model, variables) {
  for (var in variables)
    model$lhs <- cbind(model$lhs, 0)
  model$types <- c(model$types, variables)
  return (model)
}

getEvaluation <- function(perf, altVars, level, indexOfVar) {
  for (i in seq_len(nrow(altVars))) {
    if (altVars[i, indexOfVar] == 1) {
      return (perf[i, level])
    }
  }
  
  stop("Invalid arguments.")
}


#### BUILDING CONSTRAINS FOR MODEL HELPERS

###### MONOTONOUS, NORMLIZATION, EPSILON > 0

buildFirstLevelZeroConstraints <- function(perf, criteria) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrVars <- getNrVars(levels)
  
  res <- matrix(0, nrow = length(offsets), ncol = nrVars)
  
  for (i in seq_len(length(offsets))) {
    if (criteria[i] == 'g')
      res[i, offsets[i]] <- 1
    else
      res[i, offsets[i] + length(levels[[i]]) - 1] <- 1
  }
  
  return (list(lhs = res,
               dir = rep("==", length(offsets)),
               rhs = rep(0, length(offsets))))
}

buildBestLevelsAddToUnityConstraint <- function(perf, criteria) {
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  nrVars <- getNrVars(levels)
  
  lhs <- rep(0, nrVars)
  ind <- c((offsets - 1)[-1], nrVars - 1)
  
  for (i in seq_len(length(offsets))) {
    if (criteria[i] == 'g')
      lhs[offsets[i] + length(levels[[i]]) - 1] <- 1
    else
      lhs[offsets[i]] <- 1
  }
  
  return (list(lhs = lhs, dir = "==", rhs = 1))
}

buildEpsilonStrictlyPositiveConstraint <- function(nrVars, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[epsilonIndex] <- 1
  return (list(lhs = lhs, dir = ">=", rhs = RORUTADIS_MINEPS))
}

buildMonotonousAndCharacteristicPointsConstraints <- function(perf,
                                                              criteria,
                                                              characteristicPoints,
                                                              strictVF) {  
  levels <- getLevels(perf)
  offsets <- getOffsets(levels)
  epsilonIndex <- getNrVars(levels)
  linearSegments <- getNrLinearSegments(characteristicPoints)
  nrOutputVars <- epsilonIndex + sum(linearSegments)
  firstCharacteristicPointIndex <- epsilonIndex + 1
  altVars <- buildAltVariableMatrix(perf)
  
  resLhs <- c()
  resDir <- c()
  resRhs <- c()
  
  for (i in seq_len(length(levels))) {
    if (linearSegments[i] == 0) {
      for (j in seq_len(length(levels[[i]]) - 1)) {
        index <- offsets[i] + j - 1        
        lhs <- array(0, dim = nrOutputVars)
        lhs[index] <- 1
        lhs[index + 1] <- -1
        if (criteria[i] == 'g') {
          if (strictVF == TRUE) {
            lhs[epsilonIndex] <- 1
          }
          resDir <- c(resDir, "<=")
        }
        else {
          if (strictVF == TRUE) {
            lhs[epsilonIndex] <- -1
          }
          resDir <- c(resDir, ">=")
        }
        
        resLhs <- rbind(resLhs, lhs)
        resRhs <- c(resRhs, 0)
      }
    }
    else {
      # monotonous of characteristic points
      
      lhs <- array(0, dim = nrOutputVars)
      
      if (criteria[i] == 'g') {
        lhs[firstCharacteristicPointIndex] <- 1
      }
      else {
        lhs[firstCharacteristicPointIndex + linearSegments[i] - 1] <- 1
      }
      
      if (strictVF == TRUE) {
        lhs[epsilonIndex] <- -1
      }
      
      resDir <- c(resDir, ">=")
      resLhs <- rbind(resLhs, lhs)
      resRhs <- c(resRhs, 0)
      
      if (linearSegments[i] > 1) {
        for (k in 0:(linearSegments[i]-2)) {
          lhs <- array(0, dim = nrOutputVars)
          lhs[firstCharacteristicPointIndex + k] <- 1
          lhs[firstCharacteristicPointIndex + k + 1] <- -1
          if (criteria[i] == 'g') {
            if (strictVF == TRUE) {
              lhs[epsilonIndex] <- 1
            }
            resDir <- c(resDir, "<=")
          }
          else {
            if (strictVF == TRUE) {
              lhs[epsilonIndex] <- -1
            }
            resDir <- c(resDir, ">=")
          }
          resLhs <- rbind(resLhs, lhs)
          resRhs <- c(resRhs, 0)
        }
      }
      
      maximum <- max(perf[, i])
      minimum <- min(perf[, i])
      
      if (criteria[i] == 'g') {
        for (j in seq_len(length(levels[[i]]) - 1)) {
          index <- offsets[i] + j
          
          x <- getEvaluation(perf, altVars, i, index)
          
          for (k in seq_len(linearSegments[i])) {
            segmentUpperBound <- minimum + (((maximum - minimum) * k) / linearSegments[i])
            
            if (x > segmentUpperBound && k == linearSegments[i]) {
              segmentUpperBound <- maximum
            }
            
            if (x <= segmentUpperBound) {
              segmentLowerBound <- minimum
              
              if (k > 1) {
                segmentLowerBound <- minimum + (((maximum - minimum) * (k - 1)) / linearSegments[i])
              }
              
              lhs <- array(0, dim = nrOutputVars)
              lhs[index] <- -1
              lhs[firstCharacteristicPointIndex + k - 1] <- ((x - segmentLowerBound) / (segmentUpperBound - segmentLowerBound))
              
              if (k > 1) {
                lhs[firstCharacteristicPointIndex + k - 2] <- ((segmentLowerBound - x) / (segmentUpperBound - segmentLowerBound)) + 1
              }
              
              resLhs <- rbind(resLhs, lhs)
              resDir <- c(resDir, "==")
              resRhs <- c(resRhs, 0)
              
              break
            }
          }
        }
      }
      else {
        for (j in seq_len(length(levels[[i]]) - 1)) {
          index <- offsets[i] + j - 1
          
          x <- getEvaluation(perf, altVars, i, index)
          
          for (k in seq_len(linearSegments[i])) {
            segmentUpperBound <- minimum + (((maximum - minimum) * k) / linearSegments[i])
            
            if (x > segmentUpperBound && k == linearSegments[i]) {
              segmentUpperBound <- maximum
            }
            
            if (x <= segmentUpperBound) {
              segmentLowerBound <- minimum
              
              if (k > 1) {
                segmentLowerBound <- minimum + (((maximum - minimum) * (k - 1)) / linearSegments[i])
              }
              
              lhs <- array(0, dim = nrOutputVars)
              lhs[index] <- -1
              lhs[firstCharacteristicPointIndex + k - 1] <- ((segmentUpperBound - x) / (segmentUpperBound - segmentLowerBound))
              
              if (k < linearSegments[i]) {
                lhs[firstCharacteristicPointIndex + k] <- ((x - segmentUpperBound) / (segmentUpperBound - segmentLowerBound)) + 1
              }
              
              resLhs <- rbind(resLhs, lhs)
              resDir <- c(resDir, "==")
              resRhs <- c(resRhs, 0)
              
              break
            }
          }
        }
      }
      
      firstCharacteristicPointIndex <- firstCharacteristicPointIndex + linearSegments[i]
    }
  }
  
  return (list(lhs = resLhs, dir = resDir, rhs = resRhs))
}

###### THRESHOLDS

buildFirstThresholdGraterThen0Constraint <- function(nrVars, firstThresholdIndex, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[firstThresholdIndex] <- 1
  lhs[epsilonIndex] <- -1
  
  return (list(lhs = lhs, dir = ">=", rhs = 0))
}

buildLastThresholdLessThen1Constraint <- function(nrVars, firstThresholdIndex,
                                                  lastThresholdIndex, epsilonIndex) {
  lhs <- rep(0, nrVars)
  lhs[lastThresholdIndex] <- 1
  lhs[epsilonIndex] <- 1
  
  return (list(lhs = lhs, dir = "<=", rhs = 1))
}

buildMonotonousThresholdsConstraints <- function(nrVars, firstThresholdIndex,
                                                 lastThresholdIndex, epsilonIndex) {
  res <- c()
  
  for (i in seq_len(lastThresholdIndex - firstThresholdIndex)) {
    h <- firstThresholdIndex + i
    lhs <- rep(0, nrVars)
    lhs[h] <- 1
    lhs[h - 1] <- -1
    lhs[epsilonIndex] <- -1
    res <- rbind(res, lhs)
  }
  
  if (is.null(res))
    return (NULL)
  else
    return (list(lhs = res, dir = rep(">=", nrow(res)), rhs = rep(0, nrow(res))))
}

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

buildassignmentPairwiseAtLeastComparisonsConstraints <- function(alternativeA,
                                                                 alternativeB,
                                                                 k,
                                                                 altVars,
                                                                 firstThresholdIndex,
                                                                 lastThresholdIndex,
                                                                 firstBinaryVarIndex,
                                                                 epsilonIndex) {
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

buildClassCardinalitiesHelperConstraints <- function(alternative,
                                                     altVars,
                                                     firstThresholdIndex,
                                                     lastThresholdIndex,
                                                     firstBinaryVarForThisAlternativeIndex,
                                                     epsilonIndex) {  
  lhsData <- c()
  dirData <- c()
  rhsData <- c()
  
  sumLhs <- rep(0, ncol(altVars))
  
  for (i in 0:(lastThresholdIndex - firstThresholdIndex + 1)) {
    th_1 <- firstThresholdIndex + i - 1
    th <- firstThresholdIndex + i
    
    if (th_1 >= firstThresholdIndex) {
      lhs <- altVars[alternative, ]
      lhs[th_1] <- -1
      lhs[firstBinaryVarForThisAlternativeIndex + i] <- -RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, ">=")
      rhsData <- c(rhsData,-RORUTADIS_BIGM)
    }
    
    if (th <= lastThresholdIndex) {
      lhs <- altVars[alternative, ]
      lhs[th] <- -1
      lhs[epsilonIndex] <- 1
      lhs[firstBinaryVarForThisAlternativeIndex + i] <- RORUTADIS_BIGM
      lhsData <- rbind(lhsData, lhs)
      dirData <- c(dirData, "<=")
      rhsData <- c(rhsData, RORUTADIS_BIGM)
    }
    
    sumLhs[firstBinaryVarForThisAlternativeIndex + i] <- 1
  }
  
  lhsData <- rbind(lhsData, sumLhs)
  dirData <- c(dirData, "==")
  rhsData <- c(rhsData, 1)
  
  return (list(lhs = lhsData, dir = dirData, rhs = rhsData))
}

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

###### REPRESENTATIVE FUNCTION - CONSTRAINTS

buildUtilityDifferenceConstraint <- function(alternativeA, alternativeB,
                                             altVars, nrVariables) {
  result <- altVars[alternativeA, ]
  
  for (k in 1:length(altVars[alternativeB, ]))
    result[k] <- result[k] - altVars[alternativeB, k]
  
  return (c(result, rep(0, nrVariables - ncol(altVars))))
}

buildUtilityMultipleDifferenceConstraint <- function(alternativeA, alternativeB,
                                                     alternativeC, alternativeD,
                                                     altVars, nrVariables) {
  result <- altVars[alternativeA, ]
  
  for (k in 1:length(altVars[alternativeB, ])) {
    result[k] <- result[k] - altVars[alternativeB, k] +
      altVars[alternativeC, k] - altVars[alternativeD, k]
  }
  
  return (c(result, rep(0, nrVariables - ncol(altVars))))
}

###### CONSTRAINTS HELPERS

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
        lhs[k - 1] <- 1
        lhs[k] <- -1
      } else {
        lhs[k - 1] <- -1
        lhs[k] <- 1
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
    epsilonIndex = epsilonIndex,
    firstThresholdIndex = firstThresholdIndex,
    chPoints = chPoints,
    perfToModelVariables = perfToModelVariables,
    prefInfoToConstraints = list(),
    nrClasses = problem$nrClasses
  )
  
  # preference information
  
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
  
  # todo: the rest of pref info to implement

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

#### EXPLANATIONS HELPERS

#' Remove constraints indices by restriction indices
#' 
#' This function allows to remove constraints indices from indices interval by restriction
#' indices.
#' @param constraintIntervalIndices Vector of interval indices of each restriction
#' constraints. c(a_1, b_1, ..., a_n, b_n), where i-th of n restrictions is represented as
#' model constraints at indices between a_i and b_i including a_i, b_i.
#' @param restrictionToRemoveIndices Vector of indices of restrictions to remove.
#' @return Vector of model constraints of restrictions which are NOT in restrictionToRemoveIndices.
removeConstraintsByRestrictions <- function(constraintIntervalIndices, restrictionToRemoveIndices) {
  res <- c()
  nrRestrictions <- length(constraintIntervalIndices) / 2
  
  for (i in 1:nrRestrictions) {
    if (!(i %in% restrictionToRemoveIndices)) {
      res <- c(res, seq(constraintIntervalIndices[2 * i - 1], constraintIntervalIndices[2 * i]))
    }
  }
  
  return (res)
}

