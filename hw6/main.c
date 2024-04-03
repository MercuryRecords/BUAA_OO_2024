#include <stdio.h>
#include <string.h>
#include <malloc.h>
#include <stdlib.h>

#define MAX_INPUT_INSTR_CNT 500 
#define MAX_PERSON_ELEVATOR 8
#define ELEVATOR_CNT 6

typedef struct Person
{
        int personId;
        int start;
        int dest;
        int requestDone;
} Person;
typedef struct Elevator
{
        int passengersById[MAX_PERSON_ELEVATOR];
        int dlen;
        int floor;
        int doorOpen;
        int openTime;
        int arriveTime;
        int received;
        int resetting;
        int capacity;
        int speed;
        int toSetCapacity;
        int toSetSpeed;
        int toReset;
        int acceptTime;
        int resetTime;
        int moves;
} Elevator;
typedef char *String;

Person persons[MAX_INPUT_INSTR_CNT];
// int correct[MAX_INPUT_INSTR_CNT];
int pLen = 0;
Elevator elevators[ELEVATOR_CNT + 1];

String newString(int size);
void readInputData(FILE *src);
int checkOutputData(FILE *src);

int main(int argc, char *argv[])
{
        String inputName;
        String outputName;

        if (argc == 3)
        {
                inputName = argv[1];
                outputName = argv[2];
        }
        else
        {
                inputName = "stdin.txt";
                outputName = "stdout.txt";
        }


        FILE *inputFile = fopen(inputName, "r");

        readInputData(inputFile);
        fclose(inputFile);

        FILE *outputFile = fopen(outputName, "r");
        int chkRes = checkOutputData(outputFile);

        if (chkRes == 0)
        {
                printf("Oh! Some errors.\n");
        }
        else
        {
                printf("Correct.\n");
        }
        fclose(outputFile);
        if (chkRes == 0)
        {
                return 1;
        }
        return 0;
}

int checkOutputString(String src);
String getLine(FILE *src);

int checkOutputData(FILE *src)
{
        String tmp = newString(200);

        for (int i = 1; i <= ELEVATOR_CNT; i += 1)
        {
                elevators[i].dlen = 0;
                elevators[i].floor = 1;
                elevators[i].doorOpen = 0;
                elevators[i].received = 0;
                elevators[i].resetting = 0;
                elevators[i].capacity = 6;
                elevators[i].speed = 4000;
                elevators[i].toReset = 0;
                elevators[i].moves = 0;

        }
        // memset(correct, 0, sizeof(correct));

        tmp = getLine(src);
        while (tmp != NULL)
        {
                if (checkOutputString(tmp) == 0)
                {
                        return 0;
                }
                tmp = getLine(src);
        }

        for (int i = 0; i < pLen; i += 1)
        {
                if (persons[i].start != persons[i].dest)
                {
                        printf("Person %d not arrived, current: %d, destination: %d.\n", persons[i].personId, persons[i].start, persons[i].dest);
                        return 0;
                }
        }

        return 1;
}

String getLine(FILE *src)
{
        char ch = '\n';
        String tmp = newString(200);
        int i = 0;

        while (fscanf(src, "%c", &ch) != -1 && ch != '\n' && i < 200)
        {
                tmp[i] = ch;
                i += 1;
        }
        tmp[i] = '\0';

        if (i == 0)
        {
                return NULL;
        }

        return tmp;
}

int passTime(String *src);
int checkArrive(String src, int arriveTime);
int checkOpen(String src, int openTime);
int checkClose(String src, int closeTime);
int checkPersonIn(String src);
int checkPersonOut(String src);
int checkReceive(String src);
void setConfig(String src, int acceptTime);
int checkResetBegin(String src, int beginTime);
int checkResetEnd(String src, int endTime);

int checkOutputString(String src)
{ 
        // printf("%s\n", src);
        int tmpTime = passTime(&src);
        if (strncmp(src, "ARRIVE", 6) == 0)
        {
                int chkRes = checkArrive(src, tmpTime);
                if (chkRes == 0)
                {
                        return 0;
                }
        }
        else if (strncmp(src, "OPEN", 4) == 0)
        {
                int chkRes = checkOpen(src, tmpTime);
                if (chkRes == 0)
                {
                        return 0;
                }
        }
        else if (strncmp(src, "CLOSE", 5) == 0)
        {
                int chkRes = checkClose(src, tmpTime);
                if (chkRes == 0)
                {
                        return 0;
                }
        }
        else if (strncmp(src, "IN", 2) == 0)
        {
                int chkRes = checkPersonIn(src);
                if (chkRes == 0)
                {
                        return 0;
                }
        }
        else if (strncmp(src, "OUT", 3) == 0)
        {
                int chkRes = checkPersonOut(src);
                if (chkRes == 0)
                {
                        return 0;
                }
        } else if (strncmp(src, "RECEIVE", 7) == 0)
        {
                int chkRes = checkReceive(src);
                if (chkRes == 0)
                {
                        return 0;
                }
        } else if (strncmp(src, "RESET_ACCEPT", 12) == 0)
        {
                // set config instead of check 
                setConfig(src, tmpTime);
                return 1;
        } else if (strncmp(src, "RESET_BEGIN", 11) == 0)
        {
                int chkRes = checkResetBegin(src, tmpTime);
                if (chkRes == 0)
                {
                        return 0;
                }
        } else if (strncmp(src, "RESET_END", 9) == 0)
        {
                int chkRes = checkResetEnd(src, tmpTime);
                if (chkRes == 0)
                {
                        return 0;
                }
        }
        
}

int parseNextInt(String *src);
int findPersonInElevator(Elevator *ele, int pId);
void removePersonElevator(Elevator *ele, int pId);
int personEql(Person *p0, Person *p1);
int findPersonById(int id);

int checkPersonOut(String src)
{
        int pId = parseNextInt(&src);
        int place = parseNextInt(&src);
        int eleId = parseNextInt(&src);
        int pIndex = -1;

        Elevator *curEle = &elevators[eleId];

        if (elevators[eleId].resetting == 1) {
                printf("Elevator%d, Person%d: out when resetting.\n", eleId);
                return 0;
        }
        if (curEle->floor != place)
        {
                printf("Elevator%d, Person%d: Not arrive at %d.\n", eleId, pId, place);
                return 0;
        }
        if (curEle->doorOpen == 0)
        {
                printf("Elevator%d, Person%d: Door not open at %d.\n", eleId, pId, place);
                return 0;
        }
        pIndex = findPersonInElevator(curEle, pId);
        if (pIndex == -1)
        {
                printf("Elevator%d, Person%d: Person not in elevator at %d.\n", eleId, pId, place);
                return 0;
        }

        int curPersonId = curEle->passengersById[pIndex];
        
        int index = findPersonById(curPersonId);
        
        if (index == -1) 
        {
        	printf("Elevator%d, Person%d: Person not in input at %d.\n", eleId, pId, place);
            	return 0;
	}

        persons[index].start = place;
        // printf("Person %d arrived at %d\n", curPersonId, place);

        // if (!chkPersonCorrect(curPerson))
        // {
        //         printf("Person %d from %d to %d by %d is incorrect.\n",
        //                curPerson->personId,
        //                curPerson->start,
        //                curPerson->dest);
        //         return 0;
        // }
        removePersonElevator(curEle, pIndex);
        elevators[eleId].received -= 1;
        return 1;
}

int findPersonById(int id)
{
        for (int i = 0; i < pLen; i += 1)
        {
                if (persons[i].personId == id)
                {
                        return i;
                }
        }
        return -1;
}

int personEql(Person *p0, Person *p1)
{
        return p0->dest == p1->dest && p0->personId == p1->personId &&
               p0->start == p1->start;
}

void personCpy(Person *dest, Person *src);

void removePersonElevator(Elevator *ele, int pIndex)
{
        for (int i = pIndex; i < ele->dlen; i += 1)
        {
                ele->passengersById[i] = ele->passengersById[i + 1];
                // personCpy(&ele->passengersById[i], &ele->passengersById[i + 1]);
        }
        ele->dlen -= 1;
}

void personCpy(Person *dest, Person *src)
{
        dest->dest = src->dest;
        dest->start = src->start;
        dest->personId = src->personId;
}

int findPersonInElevator(Elevator *ele, int pId)
{
        for (int i = 0; i < ele->dlen; i += 1)
        {
                if (ele->passengersById[i] == pId)
                {
                        return i;
                }
        }
        return -1;
}

int checkPersonIn(String src)
{
        int pId = parseNextInt(&src);
        int place = parseNextInt(&src);
        int eleId = parseNextInt(&src);

        Elevator *curEle = &elevators[eleId];

        if (elevators[eleId].resetting == 1) {
                printf("Elevator%d, Person%d: in when resetting.\n", eleId);
                return 0;
        }
        int index = findPersonById(pId);
        if (index == -1)
        {
                printf("Elevator%d, Person%d: no such person in request.\n", eleId);
                return 0;
        }
        if (persons[index].start != place)
        {
                printf("Elevator%d, Person%d: person not at %d.\n", eleId, pId, place);
                printf("%d, %d\n", persons[index].start, place);
        }
        if (curEle->floor != place)
        {
                printf("Elevator%d, Person%d: Not arrive at %d.\n", eleId, pId, place);
                return 0;
        }
        if (curEle->doorOpen == 0)
        {
                printf("Elevator%d, Person%d: Door not open at %d.\n", eleId, pId, place);
                return 0;
        }
        if (curEle->dlen == curEle->capacity)
        {
                printf("Elevator%d, Person%d: Full at %d.\n", eleId, pId, place);
                return 0;
        }

        int tmpDlen = curEle->dlen;
        // Person *curPerson = &curEle->passengersById[tmpDlen];
        curEle->passengersById[tmpDlen] = pId;
        curEle->dlen += 1;
        // printf("Elevator%d, Person%d: current size %d.\n", eleId, pId, curEle->dlen);

        return 1;
}

int checkClose(String src, int closeTime)
{
        int place = parseNextInt(&src);
        int eleId = parseNextInt(&src);

        if (elevators[eleId].resetting == 1) {
                printf("Elevator%d: closed when resetting.\n", eleId);
                return 0;
        }
        if (elevators[eleId].doorOpen == 0)
        {
                printf("Elevator%d: Door close twice at %d.\n", eleId, place);
                return 0;
        }
        if (elevators[eleId].floor != place) {
                printf("Elevator%d: Incorrect floor.\n", eleId, place);
        		return 0;
		} 
        if (closeTime - elevators[eleId].openTime < elevators[eleId].speed) {
        		printf("Elevator%d: Door close too fast.\n", eleId, place);
                return 0;
		}
        elevators[eleId].doorOpen = 0;

        return 1;
}

int checkOpen(String src, int openTime)
{
        int place = parseNextInt(&src);
        int eleId = parseNextInt(&src);

        if (elevators[eleId].resetting == 1) {
                printf("Elevator%d: opened when resetting.\n", eleId);
                return 0;
        }
        if (elevators[eleId].doorOpen == 1)
        {
                printf("Elevator%d: Door open twice at %d.\n", eleId, place);
                return 0;
        }
        if (elevators[eleId].floor != place) {
                printf("Elevator%d: Incorrect floor.\n", eleId, place);
        		return 0;
		} 
        elevators[eleId].doorOpen = 1;
        elevators[eleId].openTime = openTime;

        return 1;
}

int checkArrive(String src, int arriveTime)
{
        int place = parseNextInt(&src);
        int eleId = parseNextInt(&src);


        if (elevators[eleId].resetting == 1) {
                printf("Elevator%d: moved when resetting.\n", eleId);
                return 0;
        }
        if (elevators[eleId].received == 0) {
                printf("Elevator%d: moved when no receives.\n", eleId);
                return 0;
        }
        if (elevators[eleId].toReset == 1 && elevators[eleId].moves >= 2) {
                printf("Elevator%d: moved too much after reset accept.\n", eleId);
                return 0;
        }
        if (abs(place - elevators[eleId].floor) != 1 || place < 1 || place > 11)
        {
                printf("Elevator%d: Incorrectly move to %d.\n", eleId, place);
                return 0;
        }
        if (elevators[eleId].doorOpen == 1) {
                printf("Elevator%d: Door not closed.\n", eleId, place);
                return 0;
        }
        if (arriveTime - elevators[eleId].arriveTime < elevators[eleId].speed) {
                printf("Elevator%d: Moved too Fast (faster than %d).\n", eleId, place, elevators[eleId].speed);
                return 0;
        }
        elevators[eleId].arriveTime = arriveTime;
        elevators[eleId].floor = place;

        if (elevators[eleId].toReset == 1) {
                elevators[eleId].moves += 1;
        }

        return 1;
}


int checkReceive(String src) {
        int perId = parseNextInt(&src);
        int eleId = parseNextInt(&src);
        
        if (elevators[eleId].resetting)
        {
                printf("Receive when Resetting.\n");
                return 0;
        }
        elevators[eleId].received += 1;
        return 1;
}


int checkResetBegin(String src, int beginTime) {
        int eleId = parseNextInt(&src);

        if (elevators[eleId].toReset == 0)
        {
                printf("No reset request when begin reset.\n");
                return 0;
        }
        
        if (elevators[eleId].dlen != 0) {
                printf("Elevator not empty when begin reset.\n");
                return 0;
        }
        
        if (elevators[eleId].doorOpen == 1) {
                printf("Elevator not closed when begin reset.\n");
                return 0;
        }

        elevators[eleId].resetting = 1;
        elevators[eleId].resetTime = beginTime;

        return 1;
}

int checkResetEnd(String src, int endTime) {
        int eleId = parseNextInt(&src);

        if (elevators[eleId].toReset == 0)
        {
                printf("No reset request when begin reset.\n");
                return 0;
        }
        if (endTime - elevators[eleId].acceptTime > 50000) {
                printf("Elevator%d: Response too slow.\n", eleId);
                return 0;
        }
        if (endTime - elevators[eleId].resetTime < 12000) {
                printf("Elevator%d: Reset too fast.\n", eleId);
                return 0;
        }

        elevators[eleId].toReset = 0;
        elevators[eleId].resetting = 0;
        elevators[eleId].speed = elevators[eleId].toSetSpeed;
        elevators[eleId].capacity = elevators[eleId].toSetCapacity;

        return 1;
}

void setConfig(String src, int acceptTime) {
        int eleId = parseNextInt(&src);
        int eleCp = parseNextInt(&src);
        int speed = parseNextInt(&src); //skip zero
        speed = parseNextInt(&src);
        
        elevators[eleId].toSetCapacity = eleCp;
        elevators[eleId].toSetSpeed = speed * 1000;
        elevators[eleId].toReset = 1;
        elevators[eleId].moves = 0;
        elevators[eleId].acceptTime = acceptTime;
}

Person parsePerson(String src);

void readInputData(FILE *src)
{
        String tmp = newString(100);
        int cmpRes;
        while (fscanf(src, "%s", tmp) != -1 && pLen < MAX_INPUT_INSTR_CNT)
        {
                passTime(&tmp);
                cmpRes = strncmp(tmp, "RESET", 5);
                if (cmpRes != 0)
                {
                        // printf("%s\n", tmp);
                        persons[pLen] = parsePerson(tmp);
                        pLen += 1;
                }
        }
}


Person parsePerson(String src)
{
        Person res;

        res.personId = parseNextInt(&src);
        res.start = parseNextInt(&src);
        res.dest = parseNextInt(&src);
        // printf("%d from %d to %d\n", res.personId, res.start, res.dest);

        return res;
}

int isDigit(char ch) {
    return ch >= '0' && ch <= '9';
}

int passTime(String *src)
{
	int number = 0;
    int foundDigits = 0;
        while (**src != ']')
        {
	        if (!isDigit(**src)) {
	            (*src)++;
	            continue;
	        }
	        if (!foundDigits) {
	            while (!isDigit(**src) && **src != ']') {
	                (*src)++;
	            }
	            foundDigits = 1;
        	}
        	if (isDigit(**src)) {
            number = number * 10 + (**src - '0');
            (*src)++;
	        } else {
	            break; // �����������ַ�������ѭ��
	        }
        }
        *src += 1;
        
        return number;
}

int parseNextInt(String *src)
{
        int res = 0;
        while (!(**src <= '9' && **src >= '0'))
        {
                *src += 1;
        }
        while (**src <= '9' && **src >= '0')
        {
                res = res * 10 + **src - '0';
                *src += 1;
        }
        return res;
}

String newString(int size)
{
        return (String)malloc(size);
}
