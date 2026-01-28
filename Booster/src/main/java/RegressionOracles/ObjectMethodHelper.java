package RegressionOracles;

import spoon.reflect.declaration.CtMethod;
import spoon.reflect.declaration.CtType;
import spoon.reflect.reference.CtTypeReference;

import java.util.List;

/**
 * Object 메서드(equals, toString, hashCode) 오버라이드 감지 및 활용 Helper
 */
public class ObjectMethodHelper {
     
     private static final boolean DEBUG = false;  // 디버깅 활성화
     
     /**
      * 런타임 객체의 실제 클래스에서 equals 오버라이드를 확인
      * 컴파일 타임 타입이 Interface/Abstract인 경우, 런타임 객체의 실제 클래스에서 확인
      * 
      * @param obj 런타임 객체
      * @return equals가 의미있게 오버라이드되어 있으면 true
      */
     public static boolean hasEqualsOverrideRuntime(Object obj) {
         if (obj == null) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ❌ hasEqualsOverrideRuntime: obj is null");
             }
             return false;
         }
         
         try {
             Class<?> actualClass = obj.getClass();
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] 🔍 Checking equals override at runtime for: " + actualClass.getName());
             }
             
             // 실제 클래스의 equals 메서드 확인
             java.lang.reflect.Method equalsMethod = actualClass.getMethod("equals", Object.class);
             if (equalsMethod != null) {
                 // 선언된 클래스가 Object가 아니면 오버라이드된 것
                 Class<?> declaringClass = equalsMethod.getDeclaringClass();
                 boolean isOverridden = !declaringClass.equals(Object.class);
                 
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]   Declaring class: " + declaringClass.getName());
                     System.out.println("[ObjectMethodHelper]   Result: " + (isOverridden ? "OVERRIDE found" : "DEFAULT implementation"));
                 }
                 return isOverridden;
             }
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ⚠️  Error checking equals at runtime: " + e.getMessage());
             }
         }
         
         return false;
     }
     
     /**
      * 런타임 객체의 실제 클래스에서 toString 오버라이드를 확인
      * 컴파일 타임 타입이 Interface/Abstract인 경우, 런타임 객체의 실제 클래스에서 확인
      * 
      * @param obj 런타임 객체
      * @return toString이 의미있게 오버라이드되어 있으면 true
      */
     public static boolean hasToStringOverrideRuntime(Object obj) {
         if (obj == null) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ❌ hasToStringOverrideRuntime: obj is null");
             }
             return false;
         }
         
         try {
             Class<?> actualClass = obj.getClass();
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] 🔍 Checking toString override at runtime for: " + actualClass.getName());
             }
             
             // 실제 클래스의 toString 메서드 확인
             java.lang.reflect.Method toStringMethod = actualClass.getMethod("toString");
             if (toStringMethod != null) {
                 // 선언된 클래스가 Object가 아니면 오버라이드된 것
                 Class<?> declaringClass = toStringMethod.getDeclaringClass();
                 boolean isOverridden = !declaringClass.equals(Object.class);
                 
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]   Declaring class: " + declaringClass.getName());
                     System.out.println("[ObjectMethodHelper]   Result: " + (isOverridden ? "OVERRIDE found" : "DEFAULT implementation"));
                 }
                 return isOverridden;
             }
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ⚠️  Error checking toString at runtime: " + e.getMessage());
             }
         }
         
         return false;
     }
     
     /**
      * 런타임 객체의 toString() 결과가 의미있는 값인지 확인
      * 주소값 형태 (예: "Package@hashcode") vs 실제 데이터를 판단
      * 
      * @param obj 확인할 런타임 객체
      * @return 의미있는 toString() 결과면 true, 주소값 형태면 false
      */
     public static boolean isToStringMeaningful(Object obj) {
         if (obj == null) {
             return false;
         }
         
         try {
             String strValue = obj.toString();
             
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] 🔍 Checking if toString is meaningful:");
                 System.out.println("[ObjectMethodHelper]   Object class: " + obj.getClass().getName());
                 System.out.println("[ObjectMethodHelper]   toString() result: " + (strValue.length() > 80 ? strValue.substring(0, 80) + "..." : strValue));
             }
             
             // 1. null 문자열
             if ("null".equals(strValue)) {
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]   Result: FALSE (null string)");
                 }
                 return false;
             }
             
             // 2. 주소값 형태: "ClassName@hexcode"
             // 예: "org.jsoup.nodes.Document@1a2b3c4d"
             if (isAddressFormat(strValue)) {
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]   Result: FALSE (address format)");
                 }
                 return false;
             }
             
             // 3. 의미있는 데이터
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]   Result: TRUE (meaningful data)");
             }
             return true;
             
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]   Error calling toString(): " + e.getMessage());
             }
             return false;
         }
     }
     
     /**
      * 문자열이 주소값 형태인지 확인
      * 패턴: "fully.qualified.ClassName@hexcode"
      * 예: "java.lang.Object@1a2b3c" or "org.jsoup.nodes.Document@5c647181"
      */
     private static boolean isAddressFormat(String str) {
         if (str == null || str.isEmpty()) {
             return false;
         }
         
         // @ 기호로 분리
         int atIndex = str.lastIndexOf('@');
         if (atIndex <= 0 || atIndex >= str.length() - 1) {
             return false;
         }
         
         String beforeAt = str.substring(0, atIndex);
         String afterAt = str.substring(atIndex + 1);
         
         // 앞부분: 패키지명.클래스명 형태 확인
         // - 적어도 하나의 점(.) 포함
         // - 영문자, 숫자, $ 만 포함
         boolean validClassName = beforeAt.contains(".") && 
                                 beforeAt.matches("[a-zA-Z0-9._$]+");
         
         // 뒷부분: 16진수 형태 확인
         // - 8~16자리의 16진수 (또는 10진수)
         boolean validHashCode = afterAt.matches("[0-9a-fA-F]+") && 
                                 afterAt.length() >= 1 && 
                                 afterAt.length() <= 16;
         
         boolean result = validClassName && validHashCode;
         
         if (DEBUG && result) {
             System.out.println("[ObjectMethodHelper]   ✓ Matched address pattern:");
             System.out.println("[ObjectMethodHelper]     Class: " + beforeAt);
             System.out.println("[ObjectMethodHelper]     Hashcode: " + afterAt);
         }
         
         return result;
     }
    
    /**
     * 주어진 타입이 equals() 메서드를 의미있게 오버라이드했는지 확인
     */
    public static boolean hasEqualsOverride(CtType<?> type) {
        if (type == null) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ hasEqualsOverride: type is null");
            }
            return false;
        }
        
        String typeName = type.getQualifiedName();
        if (DEBUG) {
            System.out.println("\n[ObjectMethodHelper] 🔍 Checking equals override for: " + typeName);
        }
        
        try {
            List<CtMethod<?>> equalsMethods = type.getMethodsByName("equals");
            
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper]   Found " + equalsMethods.size() + " equals methods");
            }
            
            for (CtMethod<?> method : equalsMethods) {
                int paramCount = method.getParameters().size();
                
                if (paramCount == 1) {
                    String paramType = method.getParameters().get(0).getType().getQualifiedName();
                    if (DEBUG) {
                        System.out.println("[ObjectMethodHelper]   Checking equals with parameter type: " + paramType);
                    }
                    
                    if ("java.lang.Object".equals(paramType)) {
                        if (!isDefaultEqualsImpl(method)) {
                            if (DEBUG) {
                                System.out.println("[ObjectMethodHelper] ✅ FOUND meaningful equals override!");
                                System.out.println("[ObjectMethodHelper]   Type: " + typeName);
                            }
                            return true;
                        } else {
                            if (DEBUG) {
                                System.out.println("[ObjectMethodHelper]   ⏭️  Equals is default implementation");
                            }
                        }
                    }
                }
            }
            
            CtTypeReference<?> superClassRef = type.getSuperclass();
            if (superClassRef != null) {
                String superClassName = superClassRef.getQualifiedName();
                if (DEBUG) {
                    System.out.println("[ObjectMethodHelper]   Checking superclass: " + superClassName);
                }
                
                if (!"java.lang.Object".equals(superClassName)) {
                    CtType<?> superClass = superClassRef.getTypeDeclaration();
                    if (superClass != null) {
                        return hasEqualsOverride(superClass);
                    }
                }
            }
            
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ No equals override found for: " + typeName);
            }
            return false;
        } catch (Exception e) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ⚠️  Error checking equals: " + e.getMessage());
            }
            return false;
        }
    }
    
    /**
     * CtTypeReference에서 equals 오버라이드 확인
     */
    public static boolean hasEqualsOverride(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ hasEqualsOverride(CtTypeReference): typeRef is null");
            }
            return false;
        }
        
        if (DEBUG) {
            System.out.println("[ObjectMethodHelper] 🔄 Converting CtTypeReference: " + typeRef.getQualifiedName());
        }
        
        try {
            CtType<?> type = typeRef.getTypeDeclaration();
            if (type != null) {
                return hasEqualsOverride(type);
            } else {
                if (DEBUG) {
                    System.out.println("[ObjectMethodHelper]   ❌ Could not resolve type declaration");
                }
            }
        } catch (Exception e) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ⚠️  Error: " + e.getMessage());
            }
        }
        
        return false;
    }
    
    /**
     * toString() 메서드 오버라이드 확인
     */
    public static boolean hasToStringOverride(CtType<?> type) {
        if (type == null) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ hasToStringOverride: type is null");
            }
            return false;
        }
        
        String typeName = type.getQualifiedName();
        if (DEBUG) {
            System.out.println("\n[ObjectMethodHelper] 🔍 Checking toString override for: " + typeName);
        }
        
        try {
            List<CtMethod<?>> toStringMethods = type.getMethodsByName("toString");
            
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper]   Found " + toStringMethods.size() + " toString methods");
            }
            
            for (CtMethod<?> method : toStringMethods) {
                if (method.getParameters().isEmpty()) {
                    if (!isDefaultToStringImpl(method)) {
                        if (DEBUG) {
                            System.out.println("[ObjectMethodHelper] ✅ FOUND meaningful toString override!");
                            System.out.println("[ObjectMethodHelper]   Type: " + typeName);
                        }
                        return true;
                    } else {
                        if (DEBUG) {
                            System.out.println("[ObjectMethodHelper]   ⏭️  toString is default implementation");
                        }
                    }
                }
            }
            
            CtTypeReference<?> superClassRef = type.getSuperclass();
            if (superClassRef != null) {
                String superClassName = superClassRef.getQualifiedName();
                if (!"java.lang.Object".equals(superClassName)) {
                    CtType<?> superClass = superClassRef.getTypeDeclaration();
                    if (superClass != null) {
                        return hasToStringOverride(superClass);
                    }
                }
            }
            
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ No toString override found for: " + typeName);
            }
            return false;
        } catch (Exception e) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ⚠️  Error: " + e.getMessage());
            }
            return false;
        }
    }
    
    /**
     * CtTypeReference에서 toString 오버라이드 확인
     */
    public static boolean hasToStringOverride(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ❌ hasToStringOverride(CtTypeReference): typeRef is null");
            }
            return false;
        }
        
        if (DEBUG) {
            System.out.println("[ObjectMethodHelper] 🔄 Converting CtTypeReference: " + typeRef.getQualifiedName());
        }
        
        try {
            CtType<?> type = typeRef.getTypeDeclaration();
            if (type != null) {
                return hasToStringOverride(type);
            } else {
                if (DEBUG) {
                    System.out.println("[ObjectMethodHelper]   ❌ Could not resolve type declaration");
                }
            }
        } catch (Exception e) {
            if (DEBUG) {
                System.out.println("[ObjectMethodHelper] ⚠️  Error: " + e.getMessage());
            }
        }
        
        return false;
    }
    
     /**
      * hashCode() 메서드 오버라이드 확인
      */
     public static boolean hasHashCodeOverride(CtType<?> type) {
         if (type == null) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ❌ hasHashCodeOverride: type is null");
             }
             return false;
         }
         
         String typeName = type.getQualifiedName();
         if (DEBUG) {
             System.out.println("\n[ObjectMethodHelper] 🔍 Checking hashCode override for: " + typeName);
         }
         
         try {
             List<CtMethod<?>> hashCodeMethods = type.getMethodsByName("hashCode");
             
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]   Found " + hashCodeMethods.size() + " hashCode methods");
             }
             
             for (CtMethod<?> method : hashCodeMethods) {
                 if (method.getParameters().isEmpty()) {
                     if (DEBUG) {
                         System.out.println("[ObjectMethodHelper] ✅ FOUND hashCode override!");
                         System.out.println("[ObjectMethodHelper]   Type: " + typeName);
                     }
                     return true;  // hashCode가 있으면 대부분 오버라이드됨
                 }
             }
             
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ❌ No hashCode override found for: " + typeName);
             }
             return false;
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper] ⚠️  Error checking hashCode: " + e.getMessage());
             }
             return false;
         }
     }
    
    /**
     * CtTypeReference에서 hashCode 오버라이드 확인
     */
    public static boolean hasHashCodeOverride(CtTypeReference<?> typeRef) {
        if (typeRef == null) {
            return false;
        }
        
        try {
            CtType<?> type = typeRef.getTypeDeclaration();
            if (type != null) {
                return hasHashCodeOverride(type);
            }
        } catch (Exception e) {
            // ignore
        }
        
        return false;
    }
    
     /**
      * equals 메서드가 기본 구현인지 확인
      */
     private static boolean isDefaultEqualsImpl(CtMethod<?> method) {
         try {
             String source = method.getBody().toString();
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]   Analyzing equals method body:");
                 System.out.println("[ObjectMethodHelper]     Body length: " + source.length());
                 System.out.println("[ObjectMethodHelper]     Body: " + (source.length() > 100 ? source.substring(0, 100) + "..." : source));
             }
             
             if (source.length() < 50) {
                 if (source.contains("this ==") || source.contains("== this")) {
                     if (DEBUG) {
                         System.out.println("[ObjectMethodHelper]     Result: DEFAULT implementation (identity check only)");
                     }
                     return true;
                 }
             }
             
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]     Result: MEANINGFUL implementation detected");
             }
             return false;
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]     Error analyzing equals: " + e.getMessage());
             }
             return false;
         }
     }
    
     /**
      * toString이 기본 구현인지 확인
      */
     private static boolean isDefaultToStringImpl(CtMethod<?> method) {
         try {
             String source = method.getBody().toString();
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]   Analyzing toString method body:");
                 System.out.println("[ObjectMethodHelper]     Body length: " + source.length());
                 System.out.println("[ObjectMethodHelper]     Body: " + (source.length() > 100 ? source.substring(0, 100) + "..." : source));
             }
             
             // 기본 구현 패턴 1: getClass() + toHexString + hashCode
             if (source.contains("getClass()") && source.contains("toHexString") && source.contains("hashCode")) {
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]     Result: DEFAULT implementation (standard Object.toString pattern)");
                 }
                 return true;
             }
             
             // 기본 구현 패턴 2: 짧고 getClass만 포함
             if (source.length() < 80 && source.contains("getClass")) {
                 if (DEBUG) {
                     System.out.println("[ObjectMethodHelper]     Result: DEFAULT implementation (minimal getClass pattern)");
                 }
                 return true;
             }
             
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]     Result: MEANINGFUL implementation detected");
             }
             return false;
         } catch (Exception e) {
             if (DEBUG) {
                 System.out.println("[ObjectMethodHelper]     Error analyzing toString: " + e.getMessage());
             }
             return false;
         }
     }
}
